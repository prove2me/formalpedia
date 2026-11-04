-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_common_fixed_block
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.common_fixed_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:31.579862+00:00
-- url     : https://prove2.me/theorems/eef30a1c-a1a3-4083-9c56-3e2251c17c5d
-- title:
--   Weighted Global Oversize Overhead: common fixed block
-- statement:
--   The Weighted Global Oversize Overhead construction uses the common fixed block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L207-L215
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L207-L215

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.common_fixed_block {K : ℕ} (hK : 100000000000000000000 ≤ K) (c d N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m < microAllowance K := by sorry
