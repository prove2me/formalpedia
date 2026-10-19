-- Prove2me | Theorems.Thm_TypeDensity_divisor_count_safe
-- name    : TypeDensity.divisor_count_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:42.510208+00:00
-- url     : https://prove2.me/theorems/7e6b96d7-cbb5-4315-9f22-b7d9ace13c2a
-- title:
--   Every divisor count expression is safe at every integer `q ≥ 2`.
-- statement:
--   Every divisor count expression is safe at every integer `q ≥ 2`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L367-L386

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_expression_pow_safe
import Theorems.Thm_TypeDensity_expression_sum_safe
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

theorem TypeDensity.divisor_count_safe (n : ℕ) (offset : ℤ) (m : Pattern n) :
    (divisorCount offset m).allSafe := by sorry
