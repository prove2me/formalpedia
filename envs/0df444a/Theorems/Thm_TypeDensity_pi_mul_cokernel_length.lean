-- Prove2me | Theorems.Thm_TypeDensity_pi_mul_cokernel_length
-- name    : TypeDensity.pi_mul_cokernel_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:21.33688+00:00
-- url     : https://prove2.me/theorems/2caafdfc-e828-4da9-85b6-3dbf83dd1f0f
-- title:
--   The cokernel of multiplication by `e` on `(Π C_j) ⧸ (g)` has length `Σ_j length (C_j ⧸ (g_j, e_j))`.
-- statement:
--   The cokernel of multiplication by `e` on `(Π C_j) ⧸ (g)` has length `Σ_j length (C_j ⧸ (g_j, e_j))`.
-- source:
--   TypeDensity/Measure/Normalizer.lean#L367-L379

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_finite_length_module_card
import Theorems.Thm_TypeDensity_pi_quotient_span_linearEquiv
import Theorems.Thm_TypeDensity_quotient_mul_range_equiv
import Theorems.Thm_TypeDensity_finite_module_length_card
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.pi_mul_cokernel_length (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (ι : Type) [Fintype ι] (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] (g e : ∀ j, C j) (ℓ : ι → ℕ)
    (hℓ : ∀ j, Module.length O (C j ⧸ (Ideal.span {g j} ⊔ Ideal.span {e j})) = ℓ j) :
    Module.length O (((∀ j, C j) ⧸ Ideal.span {g}) ⧸
      LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk (Ideal.span {g}) e))) =
      ((∑ j, ℓ j : ℕ) : ℕ∞) := by sorry
