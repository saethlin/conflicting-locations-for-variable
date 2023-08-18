use core::iter;
use core::marker::PhantomData;
use core::ops::ControlFlow;
use core::u64;
use std::sync::Arc;

use crate::function::{Function, Functions, InlinedFunction};

mod function {
    use crate::LazyCell;
    use crate::{Context, Error};
    use core::iter;

    pub(crate) struct Functions<R: gimli::Reader> {
        /// List of all `DW_TAG_subprogram` details in the unit.
        pub(crate) functions: Box<
            [(
                gimli::UnitOffset<R::Offset>,
                LazyCell<Result<Function, Error>>,
            )],
        >,
        /// List of `DW_TAG_subprogram` address ranges in the unit.
        pub(crate) addresses: Box<[FunctionAddress]>,
    }

    pub(crate) struct FunctionAddress {
        pub(crate) function: usize,
    }

    pub(crate) struct Function {}

    pub(crate) struct InlinedFunction;

    impl<R: gimli::Reader> Functions<R> {
        pub(crate) fn parse() -> Result<Functions<R>, Error> {
            loop {}
        }

        #[inline(never)] // Required
        pub(crate) fn find_address(&self, probe: u64) -> Option<usize> {
            None
        }
    }

    impl Function {
        #[inline(never)] // Required
        pub(crate) fn parse<R: gimli::Reader>(
            ctx: &Context<R>,
            sections: &gimli::Dwarf<R>,
        ) -> Result<Self, Error> {
            loop {}
        }

        pub(crate) fn find_inlined_functions(
            &self,
        ) -> iter::Rev<std::vec::IntoIter<&InlinedFunction>> {
            loop {}
        }
    }
}

type Error = gimli::Error;

#[derive(Clone, Copy, PartialEq, Eq)]
enum DebugFile {
    Primary,
    Dwo,
}

pub(crate) enum LookupResult<L: LookupContinuation> {
    Load {
        load: SplitDwarfLoad,
        continuation: L,
    },
    Output(<L as LookupContinuation>::Output),
}

pub(crate) trait LookupContinuation: Sized {
    type Output;
    type Buf: gimli::Reader;

    fn resume(self, input: Option<Arc<gimli::Dwarf<Self::Buf>>>) -> LookupResult<Self>;
}

impl<L: LookupContinuation> LookupResult<L> {
    fn map<T, F: FnOnce(L::Output) -> T>(self, f: F) -> LookupResult<MappedLookup<T, L, F>> {
        match self {
            LookupResult::Output(t) => LookupResult::Output(f(t)),
            LookupResult::Load { load, continuation } => LookupResult::Load {
                load,
                continuation: MappedLookup {
                    original: continuation,
                    mutator: f,
                },
            },
        }
    }
}

/// The state necessary to perform address to line translation.
///
/// Constructing a `Context` is somewhat costly, so users should aim to reuse `Context`s
/// when performing lookups for many addresses in the same executable.
pub struct Context<R: gimli::Reader> {
    sections: Arc<gimli::Dwarf<R>>,
    unit_ranges: Box<[UnitRange]>,
    units: Box<[ResUnit<R>]>,
}

impl<R: gimli::Reader> Context<R> {
    fn find_units(&self, probe: u64) -> impl Iterator<Item = &ResUnit<R>> {
        self.find_units_range(probe).map(|(unit, _range)| unit)
    }

    fn find_units_range(
        &self,
        probe_low: u64,
    ) -> impl Iterator<Item = (&ResUnit<R>, &gimli::Range)> {
        self.unit_ranges[..]
            .iter()
            .rev()
            .take_while(move |i| probe_low < i.max_end)
            .filter_map(move |i| Some((&self.units[i.unit_id], &i.range)))
    }

    pub(crate) fn find_frames(
        &self,
        probe: u64,
    ) -> LookupResult<impl LookupContinuation<Output = Result<FrameIter<'_>, Error>, Buf = R>> {
        let mut units_iter = self.find_units(probe);
        if let Some(unit) = units_iter.next() {
            LoopingLookup::new_lookup(unit.find_function_or_location(probe, self), move |r| {
                ControlFlow::Break(match r {
                    Err(e) => Err(e),
                    Ok((Some(function), _)) => {
                        let inlined_functions = function.find_inlined_functions();
                        Ok(FrameIter(FrameIterState::Frames(FrameIterFrames {
                            inlined_functions,
                        })))
                    }
                    Ok((None, Some(location))) => {
                        Ok(FrameIter(FrameIterState::Location(Some(location))))
                    }
                    Ok((None, None)) => match units_iter.next() {
                        Some(next_unit) => {
                            return ControlFlow::Continue(
                                next_unit.find_function_or_location(probe, self),
                            );
                        }
                        None => Ok(FrameIter(FrameIterState::Empty)),
                    },
                })
            })
        } else {
            LoopingLookup::new_complete(Ok(FrameIter(FrameIterState::Empty)))
        }
    }
}

struct UnitRange {
    unit_id: usize,
    max_end: u64,
    range: gimli::Range,
}

pub struct ResUnit<R: gimli::Reader> {
    dw_unit: gimli::Unit<R>,
    funcs: LazyCell<Result<Functions<R>, Error>>,
    dwo: LazyCell<Result<Option<Box<(Arc<gimli::Dwarf<R>>, gimli::Unit<R>)>>, Error>>,
}

pub(crate) struct SplitDwarfLoad;

struct SimpleLookup<T, R, F>
where
    F: FnOnce(Option<Arc<gimli::Dwarf<R>>>) -> T,
    R: gimli::Reader,
{
    f: F,
    phantom: PhantomData<(T, R)>,
}

impl<T, R, F> SimpleLookup<T, R, F>
where
    F: FnOnce(Option<Arc<gimli::Dwarf<R>>>) -> T,
    R: gimli::Reader,
{
    fn new_complete(t: F::Output) -> LookupResult<SimpleLookup<T, R, F>> {
        LookupResult::Output(t)
    }

    fn new_needs_load(load: SplitDwarfLoad, f: F) -> LookupResult<SimpleLookup<T, R, F>> {
        LookupResult::Load {
            load,
            continuation: SimpleLookup {
                f,
                phantom: PhantomData,
            },
        }
    }
}

impl<T, R, F> LookupContinuation for SimpleLookup<T, R, F>
where
    F: FnOnce(Option<Arc<gimli::Dwarf<R>>>) -> T,
    R: gimli::Reader,
{
    type Output = T;
    type Buf = R;

    fn resume(self, v: Option<Arc<gimli::Dwarf<Self::Buf>>>) -> LookupResult<Self> {
        LookupResult::Output((self.f)(v))
    }
}

struct MappedLookup<T, L, F>
where
    L: LookupContinuation,
    F: FnOnce(L::Output) -> T,
{
    original: L,
    mutator: F,
}

impl<T, L, F> LookupContinuation for MappedLookup<T, L, F>
where
    L: LookupContinuation,
    F: FnOnce(L::Output) -> T,
{
    type Output = T;
    type Buf = L::Buf;

    fn resume(self, v: Option<Arc<gimli::Dwarf<Self::Buf>>>) -> LookupResult<Self> {
        match self.original.resume(v) {
            LookupResult::Output(t) => LookupResult::Output((self.mutator)(t)),
            LookupResult::Load { load, continuation } => LookupResult::Load {
                load,
                continuation: MappedLookup {
                    original: continuation,
                    mutator: self.mutator,
                },
            },
        }
    }
}

struct LoopingLookup<T, L, F>
where
    L: LookupContinuation,
    F: FnMut(L::Output) -> ControlFlow<T, LookupResult<L>>,
{
    continuation: L,
    mutator: F,
}

impl<T, L, F> LoopingLookup<T, L, F>
where
    L: LookupContinuation,
    F: FnMut(L::Output) -> ControlFlow<T, LookupResult<L>>,
{
    fn new_complete(t: T) -> LookupResult<Self> {
        LookupResult::Output(t)
    }

    fn new_lookup(mut r: LookupResult<L>, mut mutator: F) -> LookupResult<Self> {
        loop {
            match r {
                LookupResult::Output(l) => match mutator(l) {
                    ControlFlow::Break(t) => return LookupResult::Output(t),
                    ControlFlow::Continue(r2) => {
                        r = r2;
                    }
                },
                LookupResult::Load { load, continuation } => {
                    return LookupResult::Load {
                        load,
                        continuation: LoopingLookup {
                            continuation,
                            mutator,
                        },
                    };
                }
            }
        }
    }
}

impl<T, L, F> LookupContinuation for LoopingLookup<T, L, F>
where
    L: LookupContinuation,
    F: FnMut(L::Output) -> ControlFlow<T, LookupResult<L>>,
{
    type Output = T;
    type Buf = L::Buf;

    fn resume(self, v: Option<Arc<gimli::Dwarf<Self::Buf>>>) -> LookupResult<Self> {
        let r = self.continuation.resume(v);
        LoopingLookup::new_lookup(r, self.mutator)
    }
}

impl<R: gimli::Reader> ResUnit<R> {
    #[inline(never)]
    fn dwarf_and_unit_dwo<'unit, 'ctx: 'unit>(
        &'unit self,
        ctx: &'ctx Context<R>,
    ) -> LookupResult<
        SimpleLookup<
            Result<(DebugFile, &'unit gimli::Dwarf<R>, &'unit gimli::Unit<R>), Error>,
            R,
            impl FnOnce(
                Option<Arc<gimli::Dwarf<R>>>,
            )
                -> Result<(DebugFile, &'unit gimli::Dwarf<R>, &'unit gimli::Unit<R>), Error>,
        >,
    > {
        SimpleLookup::new_complete(match self.dwo.borrow() {
            Some(Ok(_)) => Ok((DebugFile::Primary, &*ctx.sections, &self.dw_unit)),
            Some(Err(e)) => Err(*e),
            None => {
                let process_dwo = move |dwo_dwarf: Option<Arc<gimli::Dwarf<R>>>| {
                    let dwo_dwarf = match dwo_dwarf {
                        None => return Ok(None),
                        Some(dwo_dwarf) => dwo_dwarf,
                    };
                    let mut dwo_units = dwo_dwarf.units();
                    let dwo_header = match dwo_units.next()? {
                        Some(dwo_header) => dwo_header,
                        None => return Ok(None),
                    };

                    let mut dwo_unit = dwo_dwarf.unit(dwo_header)?;
                    dwo_unit.copy_relocated_attributes(&self.dw_unit);
                    Ok(Some(Box::new((dwo_dwarf, dwo_unit))))
                };

                return SimpleLookup::new_needs_load(SplitDwarfLoad, move |dwo_dwarf| {
                    match self.dwo.borrow_with(|| process_dwo(dwo_dwarf)) {
                        Ok(_) => Ok((DebugFile::Primary, &*ctx.sections, &self.dw_unit)),
                        Err(e) => Err(*e),
                    }
                });
            }
        })
    }

    fn parse_functions_dwarf_and_unit(&self) -> Result<&Functions<R>, Error> {
        self.funcs
            .borrow_with(|| Functions::parse())
            .as_ref()
            .map_err(Error::clone)
    }

    fn find_location(&self) -> Result<Option<Location>, Error> {
        Ok(None)
    }

    #[inline(never)]
    fn find_function_or_location<'unit, 'ctx: 'unit>(
        &'unit self,
        probe: u64,
        ctx: &'ctx Context<R>,
    ) -> LookupResult<
        impl LookupContinuation<
            Output = Result<(Option<&'unit Function>, Option<Location>), Error>,
            Buf = R,
        >,
    > {
        self.dwarf_and_unit_dwo(ctx).map(move |r| {
            let (_, sections, _) = r?;
            let functions = self.parse_functions_dwarf_and_unit()?;
            let function = match functions.find_address(probe) {
                Some(address) => {
                    let function_index = functions.addresses[address].function;
                    let (_, ref function) = functions.functions[function_index];
                    Some(
                        function
                            .borrow_with(|| Function::parse(ctx, sections))
                            .as_ref()
                            .map_err(Error::clone)?,
                    )
                }
                None => None,
            };
            let location = self.find_location()?;
            Ok((function, location))
        })
    }
}

pub struct FrameIter<'ctx>(FrameIterState<'ctx>);

enum FrameIterState<'ctx> {
    Empty,
    Location(Option<Location>),
    Frames(FrameIterFrames<'ctx>),
}

struct FrameIterFrames<'ctx> {
    inlined_functions: iter::Rev<std::vec::IntoIter<&'ctx InlinedFunction>>, // Required
}

struct Location {}

use core::cell::UnsafeCell;

pub struct LazyCell<T> {
    contents: UnsafeCell<Option<T>>,
}
impl<T> LazyCell<T> {
    pub fn borrow(&self) -> Option<&T> {
        unsafe { &*self.contents.get() }.as_ref()
    }

    pub fn borrow_with(&self, closure: impl FnOnce() -> T) -> &T {
        let ptr = self.contents.get();
        if let Some(val) = unsafe { &*ptr } {
            return val;
        }

        let val = closure();
        unsafe { (*ptr).get_or_insert(val) }
    }
}

use gimli::read::EndianSlice;
use gimli::NativeEndian as Endian;

pub fn find_frames<'a>(
    ctx: &'a crate::Context<EndianSlice<'a, Endian>>,
    probe: u64,
) -> gimli::Result<crate::FrameIter<'a>> {
    let mut l = ctx.find_frames(probe);
    loop {
        let continuation = match l {
            LookupResult::Output(output) => break output,
            LookupResult::Load { continuation, .. } => continuation,
        };

        l = continuation.resume(None);
    }
}
