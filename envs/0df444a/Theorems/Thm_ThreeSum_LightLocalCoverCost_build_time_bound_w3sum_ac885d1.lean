-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCost_build_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverCost.build_time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:42.040584+00:00
-- url     : https://prove2.me/theorems/a314fddc-26e3-4e75-8f90-8065b62e7797
-- title:
--   Light Local Cover Cost: build time bound
-- statement:
--   The Light Local Cover Cost construction uses the build time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L107-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L107-L128

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverCost.build_time_bound_w3sum_ac885d1 {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverBuild.time h ≤ 10000*B^5 := by sorry
