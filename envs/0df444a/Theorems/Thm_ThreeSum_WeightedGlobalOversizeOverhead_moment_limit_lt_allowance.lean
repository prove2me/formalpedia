-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_moment_limit_lt_allowance
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.moment_limit_lt_allowance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:25.805896+00:00
-- url     : https://prove2.me/theorems/9a2e8c45-239f-4d38-81c0-819087a90b1a
-- title:
--   Weighted Global Oversize Overhead: moment limit lt allowance
-- statement:
--   The Weighted Global Oversize Overhead construction uses the moment limit lt allowance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L193-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L193-L200

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.moment_limit_lt_allowance {K : ℕ} (hK : 0 < K) :
    40/((selectedMoment K : ℝ)*Hpi) < microAllowance K := by sorry
