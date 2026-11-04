-- Prove2me | Theorems.Thm_ThreeSum_LightSourceFlagTest_flag_eq_one
-- name    : ThreeSum.LightSourceFlagTest.flag_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:34.901224+00:00
-- url     : https://prove2.me/theorems/0c30f5c6-d3b9-46b5-ae52-21e772043550
-- title:
--   Light Source Flag Test: flag eq one
-- statement:
--   The Light Source Flag Test construction uses the flag eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFlagTest.lean#L16-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFlagTest.lean#L16-L19

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceFlagTest
open Light

theorem ThreeSum.LightSourceFlagTest.flag_eq_one (card required count cap : ℕ) :
    flag card required count cap=1 ↔ card=required ∧ count≤cap := by sorry
