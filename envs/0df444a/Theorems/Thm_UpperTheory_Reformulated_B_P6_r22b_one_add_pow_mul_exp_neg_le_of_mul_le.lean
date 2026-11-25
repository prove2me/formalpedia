-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r22b_one_add_pow_mul_exp_neg_le_of_mul_le
-- name    : UpperTheory.Reformulated.B.P6.r22b.one_add_pow_mul_exp_neg_le_of_mul_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:35.492802+00:00
-- url     : https://prove2.me/theorems/756be151-2bb8-4ba0-8ab8-9abf3b83545a
-- title:
--   r22b: one add pow mul exp neg le of mul le
-- statement:
--   The r22b construction uses the one add pow mul exp neg le of mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/OneAddPowMulExpLe.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/OneAddPowMulExpLe.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_OneAddPowMulExpLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r22b

theorem UpperTheory.Reformulated.B.P6.r22b.one_add_pow_mul_exp_neg_le_of_mul_le (K : ℕ) {a β s : ℝ} (ha : 0 < a) (hKa : (K : ℝ) * a ≤ β) (hs : 0 ≤ s) :
    (1 + s) ^ K * Real.exp (-β * s) ≤ (1 + 1 / a) ^ K := by sorry
