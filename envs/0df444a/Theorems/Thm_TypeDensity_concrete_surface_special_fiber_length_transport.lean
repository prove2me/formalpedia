-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_special_fiber_length_transport
-- name    : TypeDensity.concrete_surface_special_fiber_length_transport
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:26.062211+00:00
-- url     : https://prove2.me/theorems/02889873-7478-4647-8f9c-ec121bc7a360
-- title:
--   The length of `R/(π, f)` for a concrete surface `R` equals the length of the special fibre modulo the image of `f`.
-- statement:
--   The length of `R/(π, f)` for a concrete surface `R` equals the length of the special fibre modulo the image of `f`.
-- source:
--   TypeDensity/Blowup/Charts.lean#L1117-L1156

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_surface_special_fiber_length_transport (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (f : ConcreteSurface O pi u a b) (e : (ConcreteSurface O pi u a b ⧸ Ideal.span
    {algebraMap O (ConcreteSurface O pi u a b) pi}) ≃+* SpecialFiber (IsLocalRing.ResidueField O) a
    b) :
    Module.length (ConcreteSurface O pi u a b) (ConcreteSurface O pi u a b ⧸ Ideal.span
        {algebraMap O (ConcreteSurface O pi u a b) pi, f}) = Module.length
        (SpecialFiber (IsLocalRing.ResidueField O) a b) (SpecialFiber (IsLocalRing.ResidueField O) a
        b ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span
        {algebraMap O (ConcreteSurface O pi u a b) pi}) f)}) := by sorry
