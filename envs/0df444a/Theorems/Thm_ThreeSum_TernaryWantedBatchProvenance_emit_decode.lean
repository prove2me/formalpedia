-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_emit_decode
-- name    : ThreeSum.TernaryWantedBatchProvenance.emit_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:09.029859+00:00
-- url     : https://prove2.me/theorems/bffeb940-b10d-4c1b-8ba7-529a27c509ba
-- title:
--   Ternary Wanted Batch Provenance: emit decode
-- statement:
--   The Ternary Wanted Batch Provenance construction uses the emit decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L87-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L87-L100

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchProvenance.emit_decode (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) (j) :
    emit R S words maps positions (decode P R S J raws words maps targets positions n j)=
      TernaryWantedBatchIndex.get
        (TernaryWantedBatchIndex.entries P R S J raws words maps targets positions n) j.val := by sorry
