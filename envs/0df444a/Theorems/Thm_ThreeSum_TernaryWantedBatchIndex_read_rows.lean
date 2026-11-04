-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_read_rows
-- name    : ThreeSum.TernaryWantedBatchIndex.read_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:10.544021+00:00
-- url     : https://prove2.me/theorems/03ea160b-49c2-4c28-99f8-84f867e08790
-- title:
--   Ternary Wanted Batch Index: read rows
-- statement:
--   The Ternary Wanted Batch Index construction uses the read rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L105-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L105-L112

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.read_rows {μ : ℕ → ℤ} {base : ℕ} (P R S J : ℕ) (raws : List ℤ)
    (words maps : List ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (h : Seg μ base (LightTernaryWantedBatch.rows P R S J raws words maps targets positions n))
    {i : ℕ} (hi : i < (entries P R S J raws words maps targets positions n).length) :
    let e := get (entries P R S J raws words maps targets positions n) i
    μ (base+3*i) = (e.1 : ℤ) ∧ μ (base+3*i+1) = (e.2.1 : ℤ) ∧ μ (base+3*i+2) = (e.2.2 : ℤ) := by sorry
