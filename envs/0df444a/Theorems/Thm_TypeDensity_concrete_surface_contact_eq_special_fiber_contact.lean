-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_contact_eq_special_fiber_contact
-- name    : TypeDensity.concrete_surface_contact_eq_special_fiber_contact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:52.54571+00:00
-- url     : https://prove2.me/theorems/47594948-73fc-482f-addc-641ad36aa462
-- title:
--   Contact lengths against `t` (and against `x` when `b > 0`) in the concrete surface agree with the corresponding contacts in the special fiber.
-- statement:
--   Contact lengths against `t` (and against `x` when `b > 0`) in the concrete surface agree with the corresponding contacts in the special fiber.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L813-L845

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv_parameters
import Theorems.Thm_TypeDensity_concrete_surface_vertical
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

theorem TypeDensity.concrete_surface_contact_eq_special_fiber_contact (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O, e
      (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
        (surfaceMk O pi u a b s)) =
      Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b) (residueSeries O s))
    (g : ConcreteSurface O pi u a b) :
    Module.length (ConcreteSurface O pi u a b)
    (ConcreteSurface O pi u a b ⧸ (Ideal.span {g} ⊔ Ideal.span {surfaceT O pi u a b})) =
    contact (e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})) g))
    (fiberT (IsLocalRing.ResidueField O) a b) ∧
    (0 < b →
      Module.length (ConcreteSurface O pi u a b)
      (ConcreteSurface O pi u a b ⧸ (Ideal.span {g} ⊔ Ideal.span {surfaceX O pi u a b})) =
      contact (e
        ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})) g))
      (fiberX (IsLocalRing.ResidueField O) a b)) := by sorry
