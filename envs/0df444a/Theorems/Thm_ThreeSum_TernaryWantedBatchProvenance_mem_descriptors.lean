-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_mem_descriptors
-- name    : ThreeSum.TernaryWantedBatchProvenance.mem_descriptors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:16.745583+00:00
-- url     : https://prove2.me/theorems/524bccd7-f986-4fe7-9509-94b10bcc8f77
-- title:
--   Ternary Wanted Batch Provenance: mem descriptors
-- statement:
--   The Ternary Wanted Batch Provenance construction uses the mem descriptors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L31-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L31-L48

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchProvenance.mem_descriptors (P J : ℕ) (raws : List ℤ) (targets : ℕ→ℤ) (n : ℕ)
    (d : Descriptor) : d∈descriptors P J raws targets n ↔
      d.1<n ∧ d.2∈wantedOutputs (P : ℤ) raws J (targets d.1) := by sorry
