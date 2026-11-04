-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_native_rate_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeRates.native_rate_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:41.5862+00:00
-- url     : https://prove2.me/theorems/90dd0967-cb3e-4b51-883e-b294955675ae
-- title:
--   Weighted Global Oversize Rates: native rate tendsto
-- statement:
--   The Weighted Global Oversize Rates construction uses the native rate tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L100-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L100-L111

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

theorem ThreeSum.WeightedGlobalOversizeRates.native_rate_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (nativeRate K) atTop (𝓝 ((Hpi+partitionEntropy)/2+Hpi/K)) := by sorry
