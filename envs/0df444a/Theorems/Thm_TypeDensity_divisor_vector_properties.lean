-- Prove2me | Theorems.Thm_TypeDensity_divisor_vector_properties
-- name    : TypeDensity.divisor_vector_properties
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T12:55:23.700048+00:00
-- url     : https://prove2.me/theorems/e0235275-cc5d-4fc2-989f-126aded98f43
-- title:
--   Basic properties of the divisor vector of a divisor `D` of degree `n`: the affine polynomial of `D` is monic of degree `n - D ∞`, it is the form polynomial of the divisor vector, whose entry at `n - D
-- statement:
--   Basic properties of the divisor vector of a divisor `D` of degree `n`: the affine polynomial of `D` is monic of degree `n - D ∞`, it is the form polynomial of the divisor vector, whose entry at `n - D ∞` is `1` and whose higher entries vanish.
-- source:
--   TypeDensity/Assembly/TypeEvents.lean#L795-L858

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

theorem TypeDensity.divisor_vector_properties (k : Type) [Field k] (n : ℕ) (D : ExceptionalDivisor k)
    (hD : exceptionalDegree k D = n) :
    (divisorAffinePolynomial k D).Monic ∧ (divisorAffinePolynomial k D).natDegree = n - D
      (infinityDirection k) ∧ D (infinityDirection k) ≤ n ∧ formPoly (divisorVector k n D) =
      divisorAffinePolynomial k D ∧ divisorVector k n D (⟨n - D (infinityDirection k),
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ :
      Fin (n+1)) = 1 ∧ (∀ i : Fin (n+1), n - D (infinityDirection k) < i.val → divisorVector k n D
      i = 0) ∧ divisorVector k n D ≠ 0 := by sorry
