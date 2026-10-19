-- Prove2me | Theorems.Thm_TypeDensity_unramified_adic_complete
-- name    : TypeDensity.unramified_adic_complete
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:13.467156+00:00
-- url     : https://prove2.me/theorems/31f7abc8-6001-4ead-985c-19dab7b8b854
-- title:
--   For monic `Φ` over a complete local ring, `O[X]/(Φ)` is complete and separated for the extended ideal `𝔪 O[X]/(Φ)`, and regular elements of `O` stay regular in it.
-- statement:
--   For monic `Φ` over a complete local ring, `O[X]/(Φ)` is complete and separated for the extended ideal `𝔪 O[X]/(Φ)`, and regular elements of `O` stay regular in it.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L282-L310

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_base_ideal_coordinates
import Theorems.Thm_TypeDensity_unramified_free_module
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.unramified_adic_complete (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Φ : Polynomial O) (hΦ : Φ.Monic) :
    IsAdicComplete (baseIdeal O Φ) (AdjoinRoot Φ) ∧
      (∀ x : AdjoinRoot Φ, (∀ L, x ∈ (baseIdeal O Φ)^L) → x = 0) ∧
      (∀ c : O, (∀ y : O, c * y = 0 → y = 0) →
        ∀ x : AdjoinRoot Φ, algebraMap O (AdjoinRoot Φ) c * x = 0 → x = 0) := by sorry
