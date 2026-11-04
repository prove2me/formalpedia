-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_total_eq_of_reads
-- name    : ThreeSum.LightTernaryPairedPotentialBatch.total_eq_of_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:58.49461+00:00
-- url     : https://prove2.me/theorems/1e3057e9-6e6d-43f2-a1f1-5cd61e58b5a4
-- title:
--   Light Ternary Paired Potential Batch: total eq of reads
-- statement:
--   The Light Ternary Paired Potential Batch construction uses the total eq of reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotentialBatchFinal.lean#L7-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotentialBatchFinal.lean#L7-L21

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatchFinal
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPairedPotentialBatch
open Light
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotentialBatch.total_eq_of_reads (K base Λ H : ℕ) (μ ν : ℕ→ℤ) (hΛ : 1≤Λ)
    (hread : ∀ i<H, ∀ q<Λ^4, μ (base+i*Λ^4+q)=ν (base+i*Λ^4+q)) :
    total K base Λ μ H=total K base Λ ν H := by sorry
