-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_family_charge_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeRates.family_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:41.334225+00:00
-- url     : https://prove2.me/theorems/85b7538c-78a4-4f3b-b36b-6ecefc0ecfc7
-- title:
--   Weighted Global Oversize Rates: family charge tendsto
-- statement:
--   The Weighted Global Oversize Rates construction uses the family charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L121-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L121-L126

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeRates.family_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (familyCharge K) atTop (𝓝 (8/(K : ℝ))) := by sorry
