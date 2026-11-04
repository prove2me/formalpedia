-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_depth_le_search
-- name    : ThreeSum.LightLocalCoverInitResources.depth_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:59:07.237196+00:00
-- url     : https://prove2.me/theorems/4665d7c9-c598-416f-a208-355ceff9b9a5
-- title:
--   Light Local Cover Init Resources: depth le search
-- statement:
--   The Light Local Cover Init Resources construction uses the depth le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L94-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L94-L96

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_depth_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.depth_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    512*Scales.microHalf (Scales.inputBits n)+9 ≤ Scales.localSearch 5000000 n := by sorry
