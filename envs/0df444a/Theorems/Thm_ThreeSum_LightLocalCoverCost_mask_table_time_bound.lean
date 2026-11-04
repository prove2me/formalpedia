-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCost_mask_table_time_bound
-- name    : ThreeSum.LightLocalCoverCost.mask_table_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:34.969565+00:00
-- url     : https://prove2.me/theorems/8a595f8f-9a22-4c76-9fcf-e83f0baeca90
-- title:
--   Light Local Cover Cost: mask table time bound
-- statement:
--   The Light Local Cover Cost construction uses the mask table time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean#L28-L34

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverCost.mask_table_time_bound (L n : ℕ) :
    LightMaskBitTable.time L n ≤ 400*(n+1)*(L+1)^2 := by sorry
