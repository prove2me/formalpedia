-- Prove2me | Theorems.Thm_TypeDensity_base_ideal_maximal_local
-- name    : TypeDensity.base_ideal_maximal_local
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:05.522695+00:00
-- url     : https://prove2.me/theorems/df086f1d-deea-4032-90af-137b15fdacb5
-- title:
--   For an unramified lift `Φ`, the extended ideal `𝔪 O[X]/(Φ)` is maximal, units can be detected modulo it, and `O[X]/(Φ)` is local with that maximal ideal.
-- statement:
--   For an unramified lift `Φ`, the extended ideal `𝔪 O[X]/(Φ)` is maximal, units can be detected modulo it, and `O[X]/(Φ)` is local with that maximal ideal.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L312-L337

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_unramified_adic_complete
import Theorems.Thm_TypeDensity_residue_extension_field
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

theorem TypeDensity.base_ideal_maximal_local (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (baseIdeal O Φ).IsMaximal ∧ (∀ x : AdjoinRoot Φ, IsUnit (baseReduce O Φ x) → IsUnit x) ∧
      ∃ _ : IsLocalRing (AdjoinRoot Φ),
        IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ := by sorry
