-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_fin
-- name    : ThreeSum.BlockSourceFlags.candidateIndices_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:54.14009+00:00
-- url     : https://prove2.me/theorems/369c650d-1e14-4fa8-997d-5901936b02bc
-- title:
--   Block Source Flags: candidate Indices fin
-- statement:
--   The Block Source Flags construction uses the candidate Indices fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L22-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L22-L23

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.candidateIndices_fin (h : ℕ) (s : Occurrence h) :
    candidateIndices h s.val = LightLocalCoverSchedule.candidateAt h s := by sorry

attribute [defeq] ThreeSum.BlockSourceFlags.candidateIndices_fin
