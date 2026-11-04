-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_mem_entries
-- name    : ThreeSum.TernaryWantedBatchIndex.mem_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:21.067677+00:00
-- url     : https://prove2.me/theorems/0d01da10-ce8f-4e41-b6fd-c5989f8f9b69
-- title:
--   Ternary Wanted Batch Index: mem entries
-- statement:
--   The Ternary Wanted Batch Index construction uses the mem entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L23-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L23-L46

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.mem_entries (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) (e : Entry) :
    e ∈ entries P R S J raws words maps targets positions n ↔
      ∃ t < n, e.1 = positions t ∧ (e.2.1,e.2.2) ∈
        wantedCodes (P : ℤ) raws words maps J (targets t) R S 0 1 0 1 := by sorry
