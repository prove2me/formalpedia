-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound_w3sum_ac885d1
-- name    : ThreeSum.BandCandidateRows.fromOwner_sound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:24.636804+00:00
-- url     : https://prove2.me/theorems/08cc87a7-38bb-4fce-bc86-bf7d3fc32e01
-- title:
--   Band Candidate Rows: from Owner sound
-- statement:
--   The Band Candidate Rows construction uses the from Owner sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L139-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L139-L171

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.fromOwner_sound_w3sum_ac885d1 (A B C : Family) (o : Owner A B C)
    (hf : (fromOwner A B C o).flag=1) :
    let r := fromOwner A B C o
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by sorry
