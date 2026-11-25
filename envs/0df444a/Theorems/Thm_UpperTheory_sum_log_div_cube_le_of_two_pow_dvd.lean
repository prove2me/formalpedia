-- Prove2me | Theorems.Thm_UpperTheory_sum_log_div_cube_le_of_two_pow_dvd
-- name    : UpperTheory.sum_log_div_cube_le_of_two_pow_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:20.189083+00:00
-- url     : https://prove2.me/theorems/ccc581f3-8e66-41c7-82cf-5fb65f06fa6a
-- title:
--   Upper Theory: sum log div cube le of two pow dvd
-- statement:
--   The Upper Theory construction uses the sum log div cube le of two pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/SumLogDivCubeLeOfTwoPowDvd.lean#L48-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/SumLogDivCubeLeOfTwoPowDvd.lean#L48-L123

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_SumLogDivCubeLeOfTwoPowDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators

theorem UpperTheory.sum_log_div_cube_le_of_two_pow_dvd :
    ∀ (e : ℕ), 1 ≤ e → ∀ S : Finset ℕ, (∀ l ∈ S, (2 ^ (e + 2) : ℤ) ∣ (l : ℤ) - 1 ∨ (2 ^ (e + 2) : ℤ) ∣ (l : ℤ) + 1) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 3 ≤ Real.log ((2 : ℝ) ^ e) / ((2 : ℝ) ^ e) ^ 3 := by sorry
