-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankData_Stored_heads_read
-- name    : ThreeSum.SourceBandBankData.Stored.heads_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:30.277561+00:00
-- url     : https://prove2.me/theorems/1cd8f200-504a-4e95-abd6-5ce0b97a3dfe
-- title:
--   Stored: heads read
-- statement:
--   The Stored construction uses the heads read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean#L52-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean#L52-L62

import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Theorems.Thm_ThreeSum_SourceBandPairSlices_heads_read

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankData
open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords

theorem ThreeSum.SourceBandBankData.Stored.heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g h J cut occ : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift) :
    μ base=(first base : ℤ) ∧ μ (base+1)=(SourceBandPairSlices.count NL NR g : ℤ) ∧
    μ (base+2)=(span h J cut : ℤ) ∧ μ (base+3)=(finish base NL NR g h J cut : ℤ) ∧
    μ (base+4)=(occ : ℤ) := by sorry
