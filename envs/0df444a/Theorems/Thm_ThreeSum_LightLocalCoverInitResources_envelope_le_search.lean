-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_envelope_le_search
-- name    : ThreeSum.LightLocalCoverInitResources.envelope_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:32.743739+00:00
-- url     : https://prove2.me/theorems/e219f6e9-83f7-4ca8-b048-a7a7539ad57b
-- title:
--   Light Local Cover Init Resources: envelope le search
-- statement:
--   The Light Local Cover Init Resources construction uses the envelope le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L72-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L72-L79

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by sorry
