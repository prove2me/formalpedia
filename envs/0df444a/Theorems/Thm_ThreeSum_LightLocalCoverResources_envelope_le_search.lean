-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
-- name    : ThreeSum.LightLocalCoverResources.envelope_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:19:35.610174+00:00
-- url     : https://prove2.me/theorems/d5eac20d-d3af-46de-b539-c90461322f02
-- title:
--   Light Local Cover Resources: envelope le search
-- statement:
--   The Light Local Cover Resources construction uses the envelope le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L178-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L178-L185

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000

theorem ThreeSum.LightLocalCoverResources.envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 4000000 n := by sorry
