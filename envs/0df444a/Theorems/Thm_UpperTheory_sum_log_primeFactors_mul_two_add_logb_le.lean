-- Prove2me | Theorems.Thm_UpperTheory_sum_log_primeFactors_mul_two_add_logb_le
-- name    : UpperTheory.sum_log_primeFactors_mul_two_add_logb_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:19.258299+00:00
-- url     : https://prove2.me/theorems/a80a8aff-cdd1-4235-abf7-5df47180efdb
-- title:
--   Upper Theory: sum log prime Factors mul two add logb le
-- statement:
--   The Upper Theory construction uses the sum log prime Factors mul two add logb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/SumLogPrimeFactorsMulTwoAddLogbLe.lean#L3-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/SumLogPrimeFactorsMulTwoAddLogbLe.lean#L3-L28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_SumLogPrimeFactorsMulTwoAddLogbLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.sum_log_primeFactors_mul_two_add_logb_le :
    ∀ (Q : ℕ) (y : ℝ), Q ≠ 0 → 1 ≤ y → Real.log Q ≤ y →
      (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q) ≤ 11 * y ^ 4 := by sorry
