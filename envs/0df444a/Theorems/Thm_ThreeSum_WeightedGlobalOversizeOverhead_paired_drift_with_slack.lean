-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_paired_drift_with_slack
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.paired_drift_with_slack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:05:04.985112+00:00
-- url     : https://prove2.me/theorems/b926850d-0d6a-47ce-877c-070391ff8c22
-- title:
--   Weighted Global Oversize Overhead: paired drift with slack
-- statement:
--   The Weighted Global Oversize Overhead construction uses the paired drift with slack property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L255-L261
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L255-L261

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.paired_drift_with_slack {K : ℕ} (hK : 100 ≤ K) :
    -1/(K : ℝ)+8/(K : ℝ)^2+20*(K : ℝ)*microAllowance K < 0 := by sorry
