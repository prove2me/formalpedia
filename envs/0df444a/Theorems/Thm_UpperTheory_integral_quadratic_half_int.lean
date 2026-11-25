-- Prove2me | Theorems.Thm_UpperTheory_integral_quadratic_half_int
-- name    : UpperTheory.integral_quadratic_half_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:50.168899+00:00
-- url     : https://prove2.me/theorems/02f34aeb-ab72-4679-ad33-999b2ab554c2
-- title:
--   Upper Theory: integral quadratic half int
-- statement:
--   The Upper Theory construction uses the integral quadratic half int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralQuadraticHalfInt.lean#L47-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralQuadraticHalfInt.lean#L47-L81

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralQuadraticHalfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.integral_quadratic_half_int :
    ∀ (d : ℕ), d.Prime → ∀ (a b : ℚ), IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) → ∃ x y : ℤ, Even (x - y) ∧ (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = ((x : ℂ) + (y : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) / 2 := by sorry
