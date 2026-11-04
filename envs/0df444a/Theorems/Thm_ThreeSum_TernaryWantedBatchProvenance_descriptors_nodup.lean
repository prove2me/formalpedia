-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_descriptors_nodup
-- name    : ThreeSum.TernaryWantedBatchProvenance.descriptors_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:21.233196+00:00
-- url     : https://prove2.me/theorems/3bfa3851-602c-418d-a254-7bcb5112979c
-- title:
--   Ternary Wanted Batch Provenance: descriptors nodup
-- statement:
--   The Ternary Wanted Batch Provenance construction uses the descriptors nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L50-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchProvenance.lean#L50-L62

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchProvenance.descriptors_nodup (P J : ℕ) (raws : List ℤ) (targets : ℕ→ℤ) (n : ℕ) :
    (descriptors P J raws targets n).Nodup := by sorry
