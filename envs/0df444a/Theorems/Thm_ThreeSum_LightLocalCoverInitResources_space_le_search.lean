-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_space_le_search
-- name    : ThreeSum.LightLocalCoverInitResources.space_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:30.076522+00:00
-- url     : https://prove2.me/theorems/9c378232-ca47-406b-befe-a2ac43a7fa5b
-- title:
--   Light Local Cover Init Resources: space le search
-- statement:
--   The Light Local Cover Init Resources construction uses the space le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L89-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L89-L92

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_space_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.space_le_search {n free : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.space free (Scales.microHalf (Scales.inputBits n)) ≤
      free+Scales.localSearch 5000000 n := by sorry
