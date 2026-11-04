-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_overhead_charge_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.overhead_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:02:22.840173+00:00
-- url     : https://prove2.me/theorems/bb8ff0eb-3d86-4fcd-a5a6-93f72c924cb0
-- title:
--   Weighted Global Oversize Overhead: overhead charge tendsto
-- statement:
--   The Weighted Global Oversize Overhead construction uses the overhead charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L179-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L179-L184

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeOverhead.overhead_charge_tendsto {k : ℕ} (hk : 0 < k) (c d : ℕ) :
    Tendsto (overheadCharge k c d) atTop (𝓝 (40/((k : ℝ)*Hpi))) := by sorry
