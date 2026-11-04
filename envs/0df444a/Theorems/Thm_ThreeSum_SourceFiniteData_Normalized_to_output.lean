-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_to_output
-- name    : ThreeSum.SourceFiniteData.Normalized.to_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:00.60285+00:00
-- url     : https://prove2.me/theorems/33842e8b-f573-4837-9c6e-fe33d14373bf
-- title:
--   Normalized: to output
-- statement:
--   The Normalized construction uses the to output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L64-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L64-L69

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA

theorem ThreeSum.SourceFiniteData.Normalized.to_output {μ : ℕ → ℤ} {av ae bv be cv ce tables rec vals g : ℕ} {hg : 0 < g}
    {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r) :
    LightBandRawAColor.Output μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC r := by sorry
