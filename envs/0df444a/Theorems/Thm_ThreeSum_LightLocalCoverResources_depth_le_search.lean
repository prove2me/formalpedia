-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverResources_depth_le_search
-- name    : ThreeSum.LightLocalCoverResources.depth_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:16.283623+00:00
-- url     : https://prove2.me/theorems/dba1decf-813b-4377-afcf-14d4a79f9c37
-- title:
--   Light Local Cover Resources: depth le search
-- statement:
--   The Light Local Cover Resources construction uses the depth le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L199-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L199-L201

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000

theorem ThreeSum.LightLocalCoverResources.depth_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    512*Scales.microHalf (Scales.inputBits n)+8 ≤ Scales.localSearch 4000000 n := by sorry
