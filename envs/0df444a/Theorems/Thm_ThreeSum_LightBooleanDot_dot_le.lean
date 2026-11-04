-- Prove2me | Theorems.Thm_ThreeSum_LightBooleanDot_dot_le
-- name    : ThreeSum.LightBooleanDot.dot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:09.316579+00:00
-- url     : https://prove2.me/theorems/a8681150-f499-421a-8d88-07a77ceba4d4
-- title:
--   Light Boolean Dot: dot le
-- statement:
--   The Light Boolean Dot construction uses the dot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L24-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L24-L34

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators

theorem ThreeSum.LightBooleanDot.dot_le (f g : ℕ → ℕ) {n j : ℕ}
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1) (hj : j ≤ n) :
    dot f g j ≤ j := by sorry
