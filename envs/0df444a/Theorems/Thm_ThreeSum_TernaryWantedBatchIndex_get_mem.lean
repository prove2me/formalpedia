-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_get_mem
-- name    : ThreeSum.TernaryWantedBatchIndex.get_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:14.514415+00:00
-- url     : https://prove2.me/theorems/3aa92547-0b48-4ff7-8692-8e9c1b2f56ed
-- title:
--   Ternary Wanted Batch Index: get mem
-- statement:
--   The Ternary Wanted Batch Index construction uses the get mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L67-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L67-L69

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.get_mem {xs : List Entry} {i : ℕ} (hi : i < xs.length) : get xs i ∈ xs := by sorry
