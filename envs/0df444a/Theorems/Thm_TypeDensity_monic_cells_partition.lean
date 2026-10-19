-- Prove2me | Theorems.Thm_TypeDensity_monic_cells_partition
-- name    : TypeDensity.monic_cells_partition
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:48.298316+00:00
-- url     : https://prove2.me/theorems/e72c9163-715a-4654-88fc-af1d59906a6c
-- title:
--   **Monic cell partition.** The monic polynomials of degree `n` over `O` are partitioned into the residue cells of the affine divisors of degree `n` over the residue field: there are finitely many such
-- statement:
--   **Monic cell partition.** The monic polynomials of degree `n` over `O` are partitioned into the residue cells of the affine divisors of degree `n` over the residue field: there are finitely many such divisors, every coefficient vector lies in exactly one cell, each cell is measurable of mass `q⁻ⁿ`, and the coefficient measure decomposes as a sum over cells.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L71-L149

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
import Theorems.Thm_TypeDensity_divisor_vector_properties
import Theorems.Thm_TypeDensity_monic_polynomial_divisor
import Theorems.Thm_TypeDensity_cellMeasure_apply_of_measurableSet
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_residue_cell_mass
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

theorem TypeDensity.monic_cells_partition (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    (∃ S : Finset (ExceptionalDivisor (IsLocalRing.ResidueField O)), ∀ D, D ∈ S ↔ AffineDivisor
      (IsLocalRing.ResidueField O) n D) ∧ (∀ a : Fin n → O, ∃! D : ExceptionalDivisor
      (IsLocalRing.ResidueField O), AffineDivisor (IsLocalRing.ResidueField O) n D ∧ a ∈
      residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) ∧
      (∀ D : ExceptionalDivisor (IsLocalRing.ResidueField O), AffineDivisor
      (IsLocalRing.ResidueField O) n D → MeasurableSet (residueCell O n
      (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) ∧ coefficientMeasure O n
      (residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n ∧ ∀ E : Set (Fin n → O),
      coefficientMeasure O n (E ∩ residueCell O n
      (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n * cellMeasure O n
      (residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) E) ∧ ∀ S : Finset
      (ExceptionalDivisor (IsLocalRing.ResidueField O)),
      (∀ D, D ∈ S ↔ AffineDivisor (IsLocalRing.ResidueField O) n D) → ∀ E : Set (Fin n → O),
      MeasurableSet E → coefficientMeasure O n E = ∑ D ∈ S, coefficientMeasure O n
      (E ∩ residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) := by sorry
