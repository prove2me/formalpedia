-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_mapAt
-- name    : ThreeSum.LightLocalCoverSchedule.candidateAt_mapAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:13.046222+00:00
-- url     : https://prove2.me/theorems/387e3667-6c79-47ef-89ee-73b789bdf014
-- title:
--   Light Local Cover Schedule: candidate At map At
-- statement:
--   The Light Local Cover Schedule construction uses the candidate At map At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L116-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L116-L127

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

theorem ThreeSum.LightLocalCoverSchedule.candidateAt_mapAt (h : ℕ) (s : Occurrence h) :
    candidate h (candidateAt h s) = mapAt h s := by sorry
