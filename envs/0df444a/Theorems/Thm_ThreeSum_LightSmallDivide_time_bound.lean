-- Prove2me | Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
-- name    : ThreeSum.LightSmallDivide.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:39:04.698655+00:00
-- url     : https://prove2.me/theorems/80d3bfdb-eccf-4f9a-9c8a-eb0ec7ca8c30
-- title:
--   Light Small Divide: time bound
-- statement:
--   The Light Small Divide construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSmallDivide.lean#L86-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSmallDivide.lean#L86-L89

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
set_option autoImplicit false
open ThreeSum ThreeSum.LightSmallDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSmallDivide.time_bound (a b : ℕ) : time a b ≤ 20*a+40 := by sorry
