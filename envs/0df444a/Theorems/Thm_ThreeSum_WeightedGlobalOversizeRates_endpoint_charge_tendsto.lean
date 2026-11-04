-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_endpoint_charge_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeRates.endpoint_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:06:11.125003+00:00
-- url     : https://prove2.me/theorems/21d3c0f1-1143-4041-9516-16cea152cf92
-- title:
--   Weighted Global Oversize Rates: endpoint charge tendsto
-- statement:
--   The Weighted Global Oversize Rates construction uses the endpoint charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L132-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L132-L134

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_endpoint_charge_tendsto

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeRates.endpoint_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (endpointCharge K) atTop (𝓝 (2*Halpha/Hpi+8/K)) := by sorry
