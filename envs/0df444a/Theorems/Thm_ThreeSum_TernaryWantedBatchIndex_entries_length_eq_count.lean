-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_entries_length_eq_count
-- name    : ThreeSum.TernaryWantedBatchIndex.entries_length_eq_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:53.966138+00:00
-- url     : https://prove2.me/theorems/e0e2772a-9804-4e60-bfc8-082dced68535
-- title:
--   Ternary Wanted Batch Index: entries length eq count
-- statement:
--   The Ternary Wanted Batch Index construction uses the entries length eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L71-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L71-L77

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.entries_length_eq_count (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :
    (entries P R S J raws words maps targets positions n).length =
      TernaryWantedBatchCount.count P R S J raws words maps targets n := by sorry
