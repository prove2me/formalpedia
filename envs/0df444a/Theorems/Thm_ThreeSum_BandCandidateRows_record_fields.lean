-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_record_fields
-- name    : ThreeSum.BandCandidateRows.record_fields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:29.285449+00:00
-- url     : https://prove2.me/theorems/25746f8e-66ee-4fb0-9a27-2dc469206a89
-- title:
--   Band Candidate Rows: record fields
-- statement:
--   The Band Candidate Rows construction uses the record fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L86-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean#L86-L90

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000

theorem ThreeSum.BandCandidateRows.record_fields {μ : ℕ → ℤ} {dst : ℕ} {r : Record}
    (H : Seg μ dst r.cells) :
    μ dst=(r.flag : ℤ) ∧ μ (dst+1)=(r.a : ℤ) ∧
      μ (dst+2)=(r.b : ℤ) ∧ μ (dst+3)=(r.c : ℤ) := by sorry
