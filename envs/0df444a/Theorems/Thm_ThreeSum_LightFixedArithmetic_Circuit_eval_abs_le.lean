-- Prove2me | Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_eval_abs_le
-- name    : ThreeSum.LightFixedArithmetic.Circuit.eval_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:49.843273+00:00
-- url     : https://prove2.me/theorems/ef4fd800-2368-45a4-bbdd-af1d55c7ccd8
-- title:
--   Circuit: eval abs le
-- statement:
--   The Circuit construction uses the eval abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L46-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L46-L55

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedArithmetic
open Light

theorem ThreeSum.LightFixedArithmetic.Circuit.eval_abs_le (e : Circuit) (x : ℕ → ℤ) {U : ℤ}
    (hU : 0≤U) (hx : ∀ i, |x i|≤U) : |e.eval x|≤e.bound U := by sorry
