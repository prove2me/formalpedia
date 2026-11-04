-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_rateUpper_tendsto
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.rateUpper_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:02:19.009189+00:00
-- url     : https://prove2.me/theorems/5c29995e-353c-4ec0-9991-7ddac56f46a5
-- title:
--   Weighted Global Oversize Overhead: rate Upper tendsto
-- statement:
--   The Weighted Global Oversize Overhead construction uses the rate Upper tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L158-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L158-L176

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.rateUpper_tendsto {k : ℕ} (hk : 0 < k) (c d : ℕ) :
    Tendsto (rateUpper k c d) atTop (𝓝 (20/(k : ℝ))) := by sorry
