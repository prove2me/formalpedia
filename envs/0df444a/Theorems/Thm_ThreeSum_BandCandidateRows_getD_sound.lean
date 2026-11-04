-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_getD_sound
-- name    : ThreeSum.BandCandidateRows.getD_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:39.300042+00:00
-- url     : https://prove2.me/theorems/345d9bd2-a390-4825-91c3-12e1e6e5938a
-- title:
--   Band Candidate Rows: get D sound
-- statement:
--   The Band Candidate Rows construction uses the get D sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L38-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L38-L45

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000

theorem ThreeSum.BandCandidateRows.getD_sound {A B C : Family} {s : ℕ} (hs : s < (records A B C).length)
    (hf : ((records A B C).getD s default).flag=1) :
    let r := (records A B C).getD s default
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by sorry
