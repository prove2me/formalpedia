-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner_w3sum_ac885d1
-- name    : ThreeSum.BandCandidateRows.mem_records_owner_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:28.830913+00:00
-- url     : https://prove2.me/theorems/381e4101-482b-4f58-a750-ca7160f526d7
-- title:
--   Band Candidate Rows: mem records owner
-- statement:
--   The Band Candidate Rows construction uses the mem records owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L12-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L12-L24

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000

theorem ThreeSum.BandCandidateRows.mem_records_owner_w3sum_ac885d1 {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    ∃ o : Owner A B C, fromOwner A B C o=r := by sorry
