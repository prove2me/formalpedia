-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_of_output
-- name    : ThreeSum.SourceFiniteData.Normalized.of_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:54:21.296541+00:00
-- url     : https://prove2.me/theorems/08ea44b7-cfc3-43f3-b283-68e68d1a35fc
-- title:
--   Normalized: of output
-- statement:
--   The Normalized construction uses the of output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L71-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L71-L76

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA

theorem ThreeSum.SourceFiniteData.Normalized.of_output {μ : ℕ → ℤ} {av ae bv be cv ce tables rec vals g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r : ℤ}
    (H : LightBandRawAColor.Output μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC r) :
    ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
      (B : List ℤ) (hsB : B.Pairwise (· < ·)) (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := by sorry
