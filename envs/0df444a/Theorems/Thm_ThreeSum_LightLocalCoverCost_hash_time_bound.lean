-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCost_hash_time_bound
-- name    : ThreeSum.LightLocalCoverCost.hash_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:31.469191+00:00
-- url     : https://prove2.me/theorems/06eeaafa-843e-4040-afa5-4a53eae13f4e
-- title:
--   Light Local Cover Cost: hash time bound
-- statement:
--   The Light Local Cover Cost construction uses the hash time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L12-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L12-L19

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverCost.hash_time_bound (L n p : ℕ) :
    LightHashHistogram.time L n p p ≤ 1000*(L+1)*(n+1)*(p+1) := by sorry
