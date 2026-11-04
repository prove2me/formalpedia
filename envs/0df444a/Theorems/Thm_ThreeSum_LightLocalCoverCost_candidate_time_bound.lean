-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCost_candidate_time_bound
-- name    : ThreeSum.LightLocalCoverCost.candidate_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:22.57992+00:00
-- url     : https://prove2.me/theorems/7ae0c799-3a28-4e7d-b29a-d8de4bbe125b
-- title:
--   Light Local Cover Cost: candidate time bound
-- statement:
--   The Light Local Cover Cost construction uses the candidate time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L36-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L36-L66

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverCost.candidate_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverCandidate.time L n p N ≤ 5000*B^4 := by sorry
