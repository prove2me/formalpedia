-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSchedule_leftCount_candidateAt
-- name    : ThreeSum.LightLocalCoverSchedule.leftCount_candidateAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:39.150196+00:00
-- url     : https://prove2.me/theorems/3fded675-331e-42ac-a0de-49a21ae0d2ab
-- title:
--   Light Local Cover Schedule: left Count candidate At
-- statement:
--   The Light Local Cover Schedule construction uses the left Count candidate At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L129-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L129-L133

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

theorem ThreeSum.LightLocalCoverSchedule.leftCount_candidateAt (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.leftCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) := by sorry
