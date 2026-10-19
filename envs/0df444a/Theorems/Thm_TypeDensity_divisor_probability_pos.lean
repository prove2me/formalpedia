-- Prove2me | Theorems.Thm_TypeDensity_divisor_probability_pos
-- name    : TypeDensity.divisor_probability_pos
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:43.908043+00:00
-- url     : https://prove2.me/theorems/d543fe2c-8256-420e-9a1e-360779b04376
-- title:
--   Divisor probabilities and the inverse `1 / (1 - returnWeight c)` are positive at `q ≥ 2`.
-- statement:
--   Divisor probabilities and the inverse `1 / (1 - returnWeight c)` are positive at `q ≥ 2`.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L435-L459

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_return_weight_bounds
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

theorem TypeDensity.divisor_probability_pos (q : ℕ) (hq : 2 ≤ q) (s : State) (d c : ℕ) (hc : 2 ≤ c) :
    0 < (divisorProbability s d).eval q ∧
      0 < (Expr.inv (.sub (.const 1) (returnWeight c))).eval q := by sorry
