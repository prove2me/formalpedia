-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_residue_regular_of_special_fiber
-- name    : TypeDensity.concrete_surface_residue_regular_of_special_fiber
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:45.524447+00:00
-- url     : https://prove2.me/theorems/f397647b-6f04-46ae-ab7e-6081daa5bfdf
-- title:
--   An element of the concrete surface whose image in the special fiber is a nonzerodivisor is a nonzerodivisor modulo `π`.
-- statement:
--   An element of the concrete surface whose image in the special fiber is a nonzerodivisor is a nonzerodivisor modulo `π`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L722-L736

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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

theorem TypeDensity.concrete_surface_residue_regular_of_special_fiber (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (f : ConcreteSurface O pi u a b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (hreg : Function.Injective
      (fun w : SpecialFiber (IsLocalRing.ResidueField O) a b ↦ e
        (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f) * w)) :
    Function.Injective
    (fun w : ConcreteSurface O pi u a b ⧸ Ideal.span
      {algebraMap O (ConcreteSurface O pi u a b) pi} => Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f * w) := by sorry
