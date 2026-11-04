-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSchedule_matrix_covers
-- name    : ThreeSum.LightLocalCoverSchedule.matrix_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:25:27.948513+00:00
-- url     : https://prove2.me/theorems/1867bf7d-c474-4168-8d98-6d41af45148e
-- title:
--   Light Local Cover Schedule: matrix covers
-- statement:
--   The Light Local Cover Schedule construction uses the matrix covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L66-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L66-L75

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

theorem ThreeSum.LightLocalCoverSchedule.matrix_covers (h i : ℕ) {r : ℕ} (hr : r < cols h) :
    BooleanGreedy.covers (matrix h) i r ↔
      Covers (512*h) h (localBucketCap h) (candidate h i) (target h r) := by sorry
