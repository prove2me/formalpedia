-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_decode_injective
-- name    : ThreeSum.TernaryWantedBatchProvenance.decode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:04.086669+00:00
-- url     : https://prove2.me/theorems/fe4f5bb4-3ef5-41a3-83e0-8fac7549f5fd
-- title:
--   Ternary Wanted Batch Provenance: decode injective
-- statement:
--   The Ternary Wanted Batch Provenance construction uses the decode injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L79-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L79-L85

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchProvenance.decode_injective (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) :
    Function.Injective (decode P R S J raws words maps targets positions n) := by sorry
