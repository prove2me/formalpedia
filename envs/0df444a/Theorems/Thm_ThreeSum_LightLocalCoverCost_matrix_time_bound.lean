-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCost_matrix_time_bound
-- name    : ThreeSum.LightLocalCoverCost.matrix_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:38.325935+00:00
-- url     : https://prove2.me/theorems/83bdc6e6-36da-4c3f-a6cb-3dbcd7710927
-- title:
--   Light Local Cover Cost: matrix time bound
-- statement:
--   The Light Local Cover Cost construction uses the matrix time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L68-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L68-L77

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverCost.matrix_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverMatrix.time L n p N ≤ 6000*B^5 := by sorry
