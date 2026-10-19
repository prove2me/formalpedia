-- Prove2me | Theorems.Thm_TypeDensity_cell_transport_preimage
-- name    : TypeDensity.cell_transport_preimage
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:35:23.473737+00:00
-- url     : https://prove2.me/theorems/5357dcdf-11f6-4ea5-9100-f3e51caa8415
-- title:
--   A bijection `f : S₁ → S₂` between coefficient cells that preserves `𝔪ᴸ`-congruence and the normalized masses of all congruence balls of level `L ≥ 1` transports the normalized c
-- statement:
--   A bijection `f : S₁ → S₂` between coefficient cells that preserves `𝔪ᴸ`-congruence and the normalized masses of all congruence balls of level `L ≥ 1` transports the normalized cell measure: `f⁻¹' T` has the same measure in `S₁` as `T` in `S₂`.
-- source:
--   TypeDensity/Formula/TypeTransport.lean#L119-L203

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
import Theorems.Thm_TypeDensity_coordinate_cylinder_clopen
import Theorems.Thm_TypeDensity_cellMeasure_apply_of_measurableSet
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
import Theorems.Thm_TypeDensity_finite_measures_from_cylinders
import Theorems.Thm_TypeDensity_coefficient_measure_probability
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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.cell_transport_preimage (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] [IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁]
    [Finite (IsLocalRing.ResidueField O₁)] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    [CompactSpace O₁] [T2Space O₁] [SecondCountableTopology O₁] [MeasurableSpace O₁]
    [BorelSpace O₁] (htop₁ : IsAdic (IsLocalRing.maximalIdeal O₁)) (O₂ : Type) [CommRing O₂]
    [IsDomain O₂] [IsDiscreteValuationRing O₂] [IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂]
    [Finite (IsLocalRing.ResidueField O₂)] [TopologicalSpace O₂] [IsTopologicalRing O₂]
    [CompactSpace O₂] [T2Space O₂] [SecondCountableTopology O₂] [MeasurableSpace O₂]
    [BorelSpace O₂] (htop₂ : IsAdic (IsLocalRing.maximalIdeal O₂)) (n₁ n₂ : ℕ)
    (S₁ : Set (Fin n₁ → O₁)) (S₂ : Set (Fin n₂ → O₂)) (hS₁ : MeasurableSet S₁)
    (hS₂ : MeasurableSet S₂) (h₁ : coefficientMeasure O₁ n₁ S₁ ≠ 0)
    (h₂ : coefficientMeasure O₂ n₂ S₂ ≠ 0) (f : (Fin n₁ → O₁) → (Fin n₂ → O₂))
    (hf : Set.BijOn f S₁ S₂)
    (hcong : ∀ (L : ℕ), ∀ a ∈ S₁, ∀ a' ∈ S₁, (∀ j, a j - a' j ∈ (IsLocalRing.maximalIdeal O₁) ^ L)
      ↔ ∀ j, f a j - f a' j ∈ (IsLocalRing.maximalIdeal O₂) ^ L)
    (hmass : ∀ (L : ℕ), 1 ≤ L → ∀ a ∈ S₁,
      cellMeasure O₁ n₁ S₁ {a' | ∀ j, a' j - a j ∈ (IsLocalRing.maximalIdeal O₁) ^ L} =
        cellMeasure O₂ n₂ S₂ {b | ∀ j, b j - f a j ∈ (IsLocalRing.maximalIdeal O₂) ^ L}) :
    ∀ T : Set (Fin n₂ → O₂), MeasurableSet T →
      MeasurableSet (S₁ ∩ f ⁻¹' T) ∧ cellMeasure O₁ n₁ S₁ (f ⁻¹' T) = cellMeasure O₂ n₂ S₂ T := by sorry
