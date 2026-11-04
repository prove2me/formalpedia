-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_four_envelope_le
-- name    : ThreeSum.LightLocalCoverInitResources.four_envelope_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:56.056303+00:00
-- url     : https://prove2.me/theorems/db81c2ae-9e65-4bc5-b591-4d90ee8fcb87
-- title:
--   Light Local Cover Init Resources: four envelope le
-- statement:
--   The Light Local Cover Init Resources construction uses the four envelope le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L26-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L26-L32

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.four_envelope_le (h : ℕ) :
    4*LightLocalCoverResources.envelope h ≤ envelope h := by sorry
