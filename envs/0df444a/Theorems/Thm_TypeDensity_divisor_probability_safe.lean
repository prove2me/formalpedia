-- Prove2me | Theorems.Thm_TypeDensity_divisor_probability_safe
-- name    : TypeDensity.divisor_probability_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:40.928239+00:00
-- url     : https://prove2.me/theorems/75db0b80-6ce1-498d-bfc6-f6f0bd76bbf6
-- title:
--   Every divisor probability expression is safe at every integer `q ≥ 2`.
-- statement:
--   Every divisor probability expression is safe at every integer `q ≥ 2`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L388-L409

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_expression_pow_safe
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.divisor_probability_safe (s : State) (d : ℕ) :
    (divisorProbability s d).allSafe := by sorry
