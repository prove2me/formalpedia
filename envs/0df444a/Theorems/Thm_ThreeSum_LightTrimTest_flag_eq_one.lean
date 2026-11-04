-- Prove2me | Theorems.Thm_ThreeSum_LightTrimTest_flag_eq_one
-- name    : ThreeSum.LightTrimTest.flag_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:27.0927+00:00
-- url     : https://prove2.me/theorems/5d24fef7-bf98-442f-8417-cf33e05e11e4
-- title:
--   Light Trim Test: flag eq one
-- statement:
--   The Light Trim Test construction uses the flag eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTrimTest.lean#L16-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTrimTest.lean#L16-L19

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTrimTest
set_option autoImplicit false
open ThreeSum ThreeSum.LightTrimTest
open Light

theorem ThreeSum.LightTrimTest.flag_eq_one (overlap leftCount rightCount cap : ℕ) :
    flag overlap leftCount rightCount cap=1 ↔ overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap := by sorry
