-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_read_three
-- name    : ThreeSum.TernaryWantedBatchIndex.read_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:05.103782+00:00
-- url     : https://prove2.me/theorems/b0a1da1a-6a22-4e87-8b38-cd010dd0d46d
-- title:
--   Ternary Wanted Batch Index: read three
-- statement:
--   The Ternary Wanted Batch Index construction uses the read three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L84-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L84-L103

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.read_three {μ : ℕ → ℤ} {base : ℕ} (xs : List Entry) (h : Seg μ base (cells xs))
    {i : ℕ} (hi : i < xs.length) :
    μ (base + 3 * i) = ((get xs i).1 : ℤ) ∧
      μ (base + 3 * i + 1) = ((get xs i).2.1 : ℤ) ∧ μ (base + 3 * i + 2) = ((get xs i).2.2 : ℤ) := by sorry
