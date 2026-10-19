-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv_parameters
-- name    : TypeDensity.concrete_surface_special_fiber_equiv_parameters
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:49.190835+00:00
-- url     : https://prove2.me/theorems/6782b258-a604-43ac-845e-7cff45e2c3f8
-- title:
--   A special-fiber identification compatible with reduction sends `t`, `x` and constants to the corresponding elements of `k[[T,X]]/(T^a X^b)`.
-- statement:
--   A special-fiber identification compatible with reduction sends `t`, `x` and constants to the corresponding elements of `k[[T,X]]/(T^a X^b)`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L738-L766

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

theorem TypeDensity.concrete_surface_special_fiber_equiv_parameters (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O, e
      (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
        (surfaceMk O pi u a b s)) =
      Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b) (residueSeries O s)) :
    e (Ideal.Quotient.mk _ (surfaceT O pi u a b)) = fiberT (IsLocalRing.ResidueField O) a b ∧
    e (Ideal.Quotient.mk _ (surfaceX O pi u a b)) = fiberX (IsLocalRing.ResidueField O) a b ∧
    ∀ c : O, e (Ideal.Quotient.mk _ (algebraMap O (ConcreteSurface O pi u a b) c)) =
    Ideal.Quotient.mk _ (MvPowerSeries.C (IsLocalRing.residue O c)) := by sorry
