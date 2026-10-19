-- Prove2me | Theorems.Thm_TypeDensity_point_cell_type_event
-- name    : TypeDensity.point_cell_type_event
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:44:09.093663+00:00
-- url     : https://prove2.me/theorems/fa0a0a6b-f00e-4223-ad16-d8b37a40edb8
-- title:
--   **Point cell law.** Assuming the root cell law, the residue cell of `(Φ mod π)^r` has the law `lawDescend (deg Φ) (stateLaw (single 1 r))`.
-- statement:
--   **Point cell law.** Assuming the root cell law, the residue cell of `(Φ mod π)^r` has the law `lawDescend (deg Φ) (stateLaw (single 1 r))`.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L717-L802

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
import Theorems.Thm_TypeDensity_descended_block_type_iff
import Theorems.Thm_TypeDensity_law_coeff_descend
import Theorems.Thm_TypeDensity_scale_type_valid_degree_iff
import Theorems.Thm_TypeDensity_cellMeasure_apply_of_measurableSet
import Theorems.Thm_TypeDensity_cell_transport_preimage
import Theorems.Thm_TypeDensity_scaling_image_borel_mass
import Theorems.Thm_TypeDensity_unramified_extension_measure_package
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_polynomial_congruence_and_product
import Theorems.Thm_TypeDensity_unramified_is_dvr
import Theorems.Thm_TypeDensity_block_descent_bijection
import Theorems.Thm_TypeDensity_block_descent_congruence_iff
import Theorems.Thm_TypeDensity_residue_cell_cylinder
import Theorems.Thm_TypeDensity_residue_cell_mass
import Theorems.Thm_TypeDensity_block_translation
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

theorem TypeDensity.point_cell_type_event (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) (hr : 0 < r) (n : ℕ) (hn : Φ.natDegree * r = n) (σ : FactorType) :
    MeasurableSet (residueCell O n (residuePoly O Φ ^ r) ∩ typeEvent O n σ) ∧ cellMeasure O n
      (residueCell O n (residuePoly O Φ ^ r)) (typeEvent O n σ) = densityValue
      (lawCoeff (lawDescend Φ.natDegree (stateLaw (State.single 1 r))) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by sorry
