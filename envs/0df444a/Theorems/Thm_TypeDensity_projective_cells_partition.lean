-- Prove2me | Theorems.Thm_TypeDensity_projective_cells_partition
-- name    : TypeDensity.projective_cells_partition
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:04.441199+00:00
-- url     : https://prove2.me/theorems/710b8172-3b06-47b1-af40-2fc633f20f7b
-- title:
--   **Projective cell partition.** The primitive coefficient vectors of length `n + 1` are partitioned into the projective cells of the divisors of degree `n`, each measurable with an explicit mass, and t
-- statement:
--   **Projective cell partition.** The primitive coefficient vectors of length `n + 1` are partitioned into the projective cells of the divisors of degree `n`, each measurable with an explicit mass, and the coefficient measure decomposes as a sum over cells.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L476-L549

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
import Theorems.Thm_TypeDensity_measure_inter_eq_sum_cells
import Theorems.Thm_TypeDensity_projective_divisor_count
import Theorems.Thm_TypeDensity_formPoly_coeff
import Theorems.Thm_TypeDensity_divisor_array_exists_unique
import Theorems.Thm_TypeDensity_divisor_vector_properties
import Theorems.Thm_TypeDensity_formPoly_natDegree_le
import Theorems.Thm_TypeDensity_monic_polynomial_divisor
import Theorems.Thm_TypeDensity_cellMeasure_apply_of_measurableSet
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_projective_cell_mass
import Theorems.Thm_TypeDensity_primitive_iff_residue_ne_zero
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

theorem TypeDensity.projective_cells_partition (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    (∃ S : Finset (ExceptionalDivisor (IsLocalRing.ResidueField O)), ∀ D, D ∈ S ↔ exceptionalDegree
      (IsLocalRing.ResidueField O) D = n) ∧ (∀ a : Fin (n+1) → O, primitive O a → ∃! D :
      ExceptionalDivisor (IsLocalRing.ResidueField O), exceptionalDegree
      (IsLocalRing.ResidueField O) D = n ∧ a ∈ projectiveCell O n
      (divisorVector (IsLocalRing.ResidueField O) n D)) ∧
      (∀ D : ExceptionalDivisor (IsLocalRing.ResidueField O), exceptionalDegree
      (IsLocalRing.ResidueField O) D = n → MeasurableSet
      (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) ∧ coefficientMeasure O
      (n+1) (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) =
      ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) - 1) *
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (n+1) ∧ ∀ E : Set (Fin (n+1) → O),
      coefficientMeasure O (n+1) (E ∩ projectiveCell O n
      (divisorVector (IsLocalRing.ResidueField O) n D)) = coefficientMeasure O (n+1)
      (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) * cellMeasure O (n+1)
      (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) E) ∧ ∀ S : Finset
      (ExceptionalDivisor (IsLocalRing.ResidueField O)),
      (∀ D, D ∈ S ↔ exceptionalDegree (IsLocalRing.ResidueField O) D = n) → ∀ E : Set
      (Fin (n+1) → O), MeasurableSet E → coefficientMeasure O (n+1)
      (E ∩ {a : Fin (n+1) → O | primitive O a}) = ∑ D ∈ S, coefficientMeasure O (n+1)
      (E ∩ projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) := by sorry
