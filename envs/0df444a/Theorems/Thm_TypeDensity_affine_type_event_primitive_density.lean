-- Prove2me | Theorems.Thm_TypeDensity_affine_type_event_primitive_density
-- name    : TypeDensity.affine_type_event_primitive_density
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T17:39:55.815214+00:00
-- url     : https://prove2.me/theorems/2bdadc3e-f827-4d9f-b09f-14db23c9fa52
-- title:
--   **Primitive density.** Assuming the root cell law, the relative density of the affine type event `σ` among primitive coefficient vectors is `densityValue (projectiveExpr n σ) q`.
-- statement:
--   **Primitive density.** Assuming the root cell law, the relative density of the affine type event `σ` among primitive coefficient vectors is `densityValue (projectiveExpr n σ) q`.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L1254-L1340

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Assembly_NullBridges
import Definitions.Def_TypeDensity_Assembly_TypeEvents
import Definitions.Def_TypeDensity_Assembly_MonicCells
import Theorems.Thm_TypeDensity_projective_divisor_count
import Theorems.Thm_TypeDensity_projective_cells_partition
import Theorems.Thm_TypeDensity_projective_cell_affine_type_event
import Theorems.Thm_TypeDensity_divisor_array_exists_unique
import Theorems.Thm_TypeDensity_divisor_vector_properties
import Theorems.Thm_TypeDensity_finite_field_card_primePower
import Theorems.Thm_TypeDensity_law_coeff_flatMap
import Theorems.Thm_TypeDensity_law_coeff_scale
import Theorems.Thm_TypeDensity_law_coeff_nonneg_closure
import Theorems.Thm_TypeDensity_state_law_coeff_nonneg
import Theorems.Thm_TypeDensity_projective_cell_conditional_density
import Theorems.Thm_TypeDensity_projective_normalizer_eval
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.affine_type_event_primitive_density (hroot : RootCellLaw) (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    MeasurableSet (affineTypeEvent O n σ ∩ {a : Fin (n+1) → O | primitive O a}) ∧
      coefficientMeasure O (n+1) (affineTypeEvent O n σ ∩ {a : Fin (n+1) → O | primitive O a}) /
      coefficientMeasure O (n+1) {a : Fin (n+1) → O | primitive O a} = densityValue
      (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by sorry
