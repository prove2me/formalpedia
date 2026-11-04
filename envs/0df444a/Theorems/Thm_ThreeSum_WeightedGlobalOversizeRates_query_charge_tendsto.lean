-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_query_charge_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeRates.query_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:02:01.483791+00:00
-- url     : https://prove2.me/theorems/5d980772-ed4a-4190-b8db-f82d57df6e06
-- title:
--   Weighted Global Oversize Rates: query charge tendsto
-- statement:
--   The Weighted Global Oversize Rates construction uses the query charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L136-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L136-L142

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_query_charge_tendsto

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeRates.query_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (queryCharge K) atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi+10/K)) := by sorry
