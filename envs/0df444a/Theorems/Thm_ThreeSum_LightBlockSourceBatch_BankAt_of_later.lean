-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBatch_BankAt_of_later
-- name    : ThreeSum.LightBlockSourceBatch.BankAt.of_later
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:43:38.111734+00:00
-- url     : https://prove2.me/theorems/b9f0b3f6-8c55-4f66-9cc4-b2d73a8be062
-- title:
--   Bank At: of later
-- statement:
--   The Bank At construction uses the of later property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatch.lean#L31-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatch.lean#L31-L48

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatch
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

theorem ThreeSum.LightBlockSourceBatch.BankAt.of_later {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i k : ℕ} {μ ν : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (K : KeptBut μ ν (slot base count (J*(512*h)) cut k) (base+2*k) 2)
    (hik : i < k) (hk : k < count) : BankAt ν base count cut i P shift B b A a q := by sorry
