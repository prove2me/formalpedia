-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_time_le_search
-- name    : ThreeSum.LightLocalCoverInitResources.time_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:55:23.942184+00:00
-- url     : https://prove2.me/theorems/3bb8a246-c3cc-45f1-8817-e677fdd1a8bf
-- title:
--   Light Local Cover Init Resources: time le search
-- statement:
--   The Light Local Cover Init Resources construction uses the time le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L81-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L81-L83

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_time_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_time_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.time_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by sorry
