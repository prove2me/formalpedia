-- Prove2me | Theorems.Thm_TypeDensity_pattern_divisor_count
-- name    : TypeDensity.pattern_divisor_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:43.047171+00:00
-- url     : https://prove2.me/theorems/f4778fa2-c9ff-4217-8e77-5ed3ad25b2ef
-- title:
--   For an allowed pattern over a finite field `k`, there are finitely many divisors with pattern `P`, and their number is `tangentCount s P` evaluated at `#k`.
-- statement:
--   For an allowed pattern over a finite field `k`, there are finitely many divisors with pattern `P`, and their number is `tangentCount s P` evaluated at `#k`.
-- source:
--   TypeDensity/Formula/PatternCounts.lean#L528-L552

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
import Theorems.Thm_TypeDensity_expression_prod_eval
import Theorems.Thm_TypeDensity_patternDivisors_equiv_colorings
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.pattern_divisor_count (k : Type) [Field k] [Finite k] (s : State)
    (P : TangentPattern s.degree) (hP : Allowed s P) :
    Finite (patternDivisors k s P) ∧
      ((Nat.card (patternDivisors k s P) : ℕ) : ℚ) = (tangentCount s P).eval (Nat.card k) := by sorry
