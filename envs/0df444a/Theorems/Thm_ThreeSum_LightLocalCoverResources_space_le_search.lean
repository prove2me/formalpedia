-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverResources_space_le_search
-- name    : ThreeSum.LightLocalCoverResources.space_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:56.201216+00:00
-- url     : https://prove2.me/theorems/0f9bb306-e3a4-4ddc-bb09-1f314fec58eb
-- title:
--   Light Local Cover Resources: space le search
-- statement:
--   The Light Local Cover Resources construction uses the space le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L195-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L195-L197

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LocalParameterBounds_space_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000

theorem ThreeSum.LightLocalCoverResources.space_le_search {n base : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    space base (Scales.microHalf (Scales.inputBits n)) ≤ base+Scales.localSearch 4000000 n := by sorry
