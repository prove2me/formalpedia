-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankLayout_bank_of_kept_w3sum_ac885d1
-- name    : ThreeSum.SourceBandBankLayout.bank_of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:00:56.501193+00:00
-- url     : https://prove2.me/theorems/43c23e9d-7483-4939-8c9b-e026ebaf0f75
-- title:
--   Source Band Bank Layout: bank of kept
-- statement:
--   The Source Band Bank Layout construction uses the bank of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L53-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L53-L72

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

theorem ThreeSum.SourceBandBankLayout.bank_of_kept_w3sum_ac885d1 {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i bound : ℕ} {μ ν : ℕ → ℤ} {p shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : LightBlockSourceBatch.BankAt μ base count cut i p shift B b A a q)
    (hi : i < count) (K : Kept μ ν bound) (hb : work base count (J*(512*h)) cut ≤ bound) :
    LightBlockSourceBatch.BankAt ν base count cut i p shift B b A a q := by sorry
