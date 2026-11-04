-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCost_host_time_bound
-- name    : ThreeSum.LightLocalCoverCost.host_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:43.77296+00:00
-- url     : https://prove2.me/theorems/8178c68b-ce24-4eb9-9fef-6536d3831a54
-- title:
--   Light Local Cover Cost: host time bound
-- statement:
--   The Light Local Cover Cost construction uses the host time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L79-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L79-L105

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverCost.host_time_bound {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverHost.time h ≤ 8000*B^5 := by sorry
