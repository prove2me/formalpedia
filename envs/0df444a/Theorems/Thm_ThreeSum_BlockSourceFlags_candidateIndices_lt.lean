-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_lt
-- name    : ThreeSum.BlockSourceFlags.candidateIndices_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:48.865671+00:00
-- url     : https://prove2.me/theorems/bf0527d5-b188-46c5-bc1f-40532da94fab
-- title:
--   Block Source Flags: candidate Indices lt
-- statement:
--   The Block Source Flags construction uses the candidate Indices lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L25-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L25-L27

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.candidateIndices_lt {h s : ℕ} (hs : s < scheduleSize h) :
    candidateIndices h s < LightLocalCoverSchedule.rows h := by sorry
