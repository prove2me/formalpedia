-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBatch_BankAt_reuse
-- name    : ThreeSum.LightBlockSourceBatch.BankAt.reuse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:42:53.503829+00:00
-- url     : https://prove2.me/theorems/43fb7655-00be-496f-abd9-6e03c6a2ed41
-- title:
--   Bank At: reuse
-- statement:
--   The Bank At construction uses the reuse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatch.lean#L50-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatch.lean#L50-L57

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatch
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

theorem ThreeSum.LightBlockSourceBatch.BankAt.reuse {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i : ℕ} {μ : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q q' : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (ho : outputOccurrences q = outputOccurrences q') :
    BankAt μ base count cut i P shift B b A a q' := by sorry
