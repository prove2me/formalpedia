-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_map_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverSchedule.indices_map_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:25:20.070673+00:00
-- url     : https://prove2.me/theorems/99acf0ef-34bf-4214-af34-3327b2f7b4c9
-- title:
--   Light Local Cover Schedule: indices map
-- statement:
--   The Light Local Cover Schedule construction uses the indices map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L77-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L77-L90

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

theorem ThreeSum.LightLocalCoverSchedule.indices_map_w3sum_ac885d1 (h : ℕ) : (indices h).map (candidate h) = localSchedule h := by sorry
