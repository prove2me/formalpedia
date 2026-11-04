-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_exists_index
-- name    : ThreeSum.TernaryWantedBatchIndex.exists_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:37.535309+00:00
-- url     : https://prove2.me/theorems/2d086030-843f-4a92-802c-7b4f4e518c8c
-- title:
--   Ternary Wanted Batch Index: exists index
-- statement:
--   The Ternary Wanted Batch Index construction uses the exists index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L79-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L79-L82

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.exists_index {xs : List Entry} {e : Entry} (he : e ∈ xs) :
    ∃ i < xs.length, get xs i = e := by sorry
