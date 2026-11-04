-- Prove2me | Theorems.Thm_ThreeSum_LightWeightGather_time_bound
-- name    : ThreeSum.LightWeightGather.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:34.65647+00:00
-- url     : https://prove2.me/theorems/ba1300bf-3c18-4c0e-9def-29f81f8286d8
-- title:
--   Light Weight Gather: time bound
-- statement:
--   The Light Weight Gather construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightGather.lean#L111-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightGather.lean#L111-L114

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightWeightGather
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightGather
open Light
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightGather.time_bound (rows width : ℕ) :
    time rows width ≤ 130*(rows+1)*(width+1) := by sorry
