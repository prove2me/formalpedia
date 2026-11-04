-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_base_factor_prefix_bound
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.base_factor_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:03:34.720744+00:00
-- url     : https://prove2.me/theorems/3e4bf728-c183-4a45-876a-49455759a2f8
-- title:
--   Weighted Global Oversize Overhead: base factor prefix bound
-- statement:
--   The Weighted Global Oversize Overhead construction uses the base factor prefix bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L217-L241
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L217-L241

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.base_factor_prefix_bound {K k m n j : ℕ} (hK : 0 < K) (hk : 0 < k)
    (hm : 0 < m) (hn : 1 < n) (hj : j ≤ radixLength m n) (c d : ℕ) :
    (baseFactor K k c d m : ℝ)^j ≤ (baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m := by sorry
