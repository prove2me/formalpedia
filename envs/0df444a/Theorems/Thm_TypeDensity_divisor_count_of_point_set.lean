-- Prove2me | Theorems.Thm_TypeDensity_divisor_count_of_point_set
-- name    : TypeDensity.divisor_count_of_point_set
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:59.293985+00:00
-- url     : https://prove2.me/theorems/f9c6d286-32a2-48f3-b06e-675991dc21d8
-- title:
--   Counting divisors of degree `n` with a given array `m` and support in a point set `S` that has `c δ` points of degree `δ`: their number is the product of falling factorials over multinomial factors.
-- statement:
--   Counting divisors of degree `n` with a given array `m` and support in a point set `S` that has `c δ` points of degree `δ`: their number is the product of falling factorials over multinomial factors.
-- source:
--   TypeDensity/Assembly/TypeEvents.lean#L655-L734

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
import Theorems.Thm_TypeDensity_colored_subset_count
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

theorem TypeDensity.divisor_count_of_point_set (k : Type) [Field k] [Finite k] (S : Set (ClosedDirection k))
    (c : ℕ → ℕ)
    (hc : ∀ δ : ℕ, 0 < δ → Nat.card {Q : ClosedDirection k // Q ∈ S ∧ directionDegree k
      Q = δ} = c δ) (n : ℕ) (m : Pattern n) (hm : m ∈ residuePatterns n) :
    Finite {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} ∧
      ((Nat.card {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} : ℕ) : ℚ) = ∏ i : Fin n,
      (((List.range (∑ j : Fin n, (m (i, j)).val)).map fun t => ((c (i.val + 1) : ℕ) : ℚ) -
      (t : ℚ)).prod / ∏ j : Fin n, ((Nat.factorial (m (i, j)).val : ℕ) : ℚ)) := by sorry
