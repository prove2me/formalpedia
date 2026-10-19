-- Prove2me | Theorems.Thm_TypeDensity_divisor_count_eval_of_point_count
-- name    : TypeDensity.divisor_count_eval_of_point_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:40.458115+00:00
-- url     : https://prove2.me/theorems/b2e156b7-299f-4530-b861-09b2963dbaec
-- title:
--   If the points of `S` of each degree `δ > 0` are counted by `availablePoints offset δ` at `q = |k|`, then the divisors of degree `n` supported on `S` with array `m` are counted by `divisorCount offset
-- statement:
--   If the points of `S` of each degree `δ > 0` are counted by `availablePoints offset δ` at `q = |k|`, then the divisors of degree `n` supported on `S` with array `m` are counted by `divisorCount offset m` at `q`.
-- source:
--   TypeDensity/Assembly/TypeEvents.lean#L736-L764

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
import Theorems.Thm_TypeDensity_divisor_count_of_point_set
import Theorems.Thm_TypeDensity_expression_prod_eval
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

theorem TypeDensity.divisor_count_eval_of_point_count (k : Type) [Field k] [Finite k]
    (S : Set (ClosedDirection k)) (offset : ℤ)
    (hS : ∀ δ : ℕ, 0 < δ → ((Nat.card {Q : ClosedDirection k // Q ∈ S ∧ directionDegree k Q = δ} :
      ℕ) : ℚ) = (availablePoints offset δ).eval (Nat.card k))
    (n : ℕ) (m : Pattern n) (hm : m ∈ residuePatterns n) :
    Finite {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} ∧
      ((Nat.card {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} : ℕ) : ℚ) = (divisorCount offset m).eval (Nat.card k) := by sorry
