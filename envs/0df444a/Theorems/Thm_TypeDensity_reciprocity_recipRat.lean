-- Prove2me | Theorems.Thm_TypeDensity_reciprocity_recipRat
-- name    : TypeDensity.reciprocity_recipRat
-- status  : Proved
-- author  : @asving
-- created : 2026-11-11T19:26:52.28752+00:00
-- url     : https://prove2.me/theorems/64eadfd8-b17e-4336-a09b-3b9a0e426e0d
-- title:
--   Theorem 1.2 (reciprocity) in every degree, with the automorphism `v = recipRat` (`q ↦ q⁻¹`) of `ℚ(q)`: `A_{n,σ} = v(B_{n,σ})` and `v(R_{n,σ}) = R_{n,σ}`.
-- statement:
--   **Theorem 1.2 (reciprocity), in terms of the automorphism `q ↦ q⁻¹`, in every degree.** For every `n` and every type `σ`, `A_{n,σ} = v(B_{n,σ})` and `v(R_{n,σ}) = R_{n,σ}` in `ℚ(q)`, where `v = recipRat` is the ring endomorphism of `ℚ(q)` with `v(q) = q⁻¹` (`recipRat_X`) and `A`, `B`, `R` are the rational functions of the monic, cluster and projective expressions. Unlike `recip_main`, there is no hypothesis `0 < n` and no syntactic substitution in the statement.
-- source:
--   TypeDensity/Corollaries/RationalForm.lean#L189-L201

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Cluster_Defs
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
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Measure_MemberBoxes
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Definitions.Def_TypeDensity_Recursion_RootCellLaw
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawWf_rootLaw
import Theorems.Thm_TypeDensity_lawCoef_globalLaw_false_eq_recipCoef_rootLaw
import Theorems.Thm_TypeDensity_recipCoef_lawCoef_globalLaw_true
import Theorems.Thm_TypeDensity_coeff_lawCoef_globalLaw_false
import Theorems.Thm_TypeDensity_coeff_lawCoef_globalLaw_true
import Theorems.Thm_TypeDensity_coeff_lawCoef
import Theorems.Thm_TypeDensity_recipCoef_coeff
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
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.reciprocity_recipRat (n : ℕ) (σ : FactorType) :
    (monicExpr n σ).rational = recipRat (clusterExpr n σ).rational ∧
    recipRat (projectiveExpr n σ).rational = (projectiveExpr n σ).rational := by sorry
