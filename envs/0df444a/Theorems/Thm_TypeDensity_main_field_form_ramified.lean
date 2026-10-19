-- Prove2me | Theorems.Thm_TypeDensity_main_field_form_ramified
-- name    : TypeDensity.main_field_form_ramified
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T18:17:08.892991+00:00
-- url     : https://prove2.me/theorems/d6e15b64-78ad-4804-882b-c8826ec96aef
-- title:
--   **Field form, arbitrary finite `K/ℚ_p`** (ramified allowed): with the maximal-ideal-adic compact topology on the ring of integers `𝒪_K = padicIntegers p K`, the monic and projective typ
-- statement:
--   **Field form, arbitrary finite `K/ℚ_p`** (ramified allowed): with the maximal-ideal-adic compact topology on the ring of integers `𝒪_K = padicIntegers p K`, the monic and projective type densities are the values at `q = |𝒪_K/𝔪|` of the rational functions `(monicExpr n σ).rational`, `(projectiveExpr n σ).rational`.
-- source:
--   TypeDensity/Main.lean#L93-L118

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
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Measure_MemberBoxes
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Definitions.Def_TypeDensity_Recursion_RootCellLaw
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_finite_field_card_primePower
import Theorems.Thm_TypeDensity_global_rational_eval
import Theorems.Thm_TypeDensity_main_dvr
import Theorems.Thm_TypeDensity_padicIntegers_maximal_adic_complete
import Theorems.Thm_TypeDensity_padicIntegers_residueField_finite
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

theorem TypeDensity.main_field_form_ramified (n : ℕ) (σ : FactorType) (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    [TopologicalSpace (padicIntegers p K)] [IsTopologicalRing (padicIntegers p K)]
    [CompactSpace (padicIntegers p K)] [T2Space (padicIntegers p K)]
    [SecondCountableTopology (padicIntegers p K)] [MeasurableSpace (padicIntegers p K)]
    [BorelSpace (padicIntegers p K)]
    (had : letI := padicIntegers_isDVR p K; IsAdic (IsLocalRing.maximalIdeal (padicIntegers p K))) :
    letI := padicIntegers_isDVR p K
    monicDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (IsLocalRing.ResidueField (padicIntegers p K)) : ℚ) (monicExpr n σ).rational :
          ℚ) : ℝ) ∧
      projectiveDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (IsLocalRing.ResidueField (padicIntegers p K)) : ℚ)
          (projectiveExpr n σ).rational : ℚ) : ℝ) := by sorry
