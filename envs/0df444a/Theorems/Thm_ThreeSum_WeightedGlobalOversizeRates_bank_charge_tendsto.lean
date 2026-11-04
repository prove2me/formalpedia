-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_bank_charge_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeRates.bank_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:01:50.085924+00:00
-- url     : https://prove2.me/theorems/7f1fe995-e7e2-400e-a70d-945d7a2d94f7
-- title:
--   Weighted Global Oversize Rates: bank charge tendsto
-- statement:
--   The Weighted Global Oversize Rates construction uses the bank charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L128-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L128-L130

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_bank_charge_tendsto

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeRates.bank_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (bankCharge K) atTop (𝓝 (2*bankEntropy/Hpi+8/K)) := by sorry
