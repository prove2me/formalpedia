-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_records_sound
-- name    : ThreeSum.BandCandidateRows.records_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:51.606699+00:00
-- url     : https://prove2.me/theorems/b09aa4e5-fc43-493c-8fb5-a94d3875671f
-- title:
--   Band Candidate Rows: records sound
-- statement:
--   The Band Candidate Rows construction uses the records sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L26-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L26-L31

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000

theorem ThreeSum.BandCandidateRows.records_sound {A B C : Family} {r : Record}
    (hr : r ∈ records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by sorry
