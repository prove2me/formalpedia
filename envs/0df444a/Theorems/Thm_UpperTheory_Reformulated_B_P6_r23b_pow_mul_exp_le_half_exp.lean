-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r23b_pow_mul_exp_le_half_exp
-- name    : UpperTheory.Reformulated.B.P6.r23b.pow_mul_exp_le_half_exp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:38.767066+00:00
-- url     : https://prove2.me/theorems/5bc2ac7c-c2b0-4427-849c-1e59fba8c6cc
-- title:
--   r23b: pow mul exp le half exp
-- statement:
--   The r23b construction uses the pow mul exp le half exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowMulExpLeHalfExp.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowMulExpLeHalfExp.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowMulExpLeHalfExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r23b

theorem UpperTheory.Reformulated.B.P6.r23b.pow_mul_exp_le_half_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : ℝ), 0 ≤ x →
      (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) := by sorry
