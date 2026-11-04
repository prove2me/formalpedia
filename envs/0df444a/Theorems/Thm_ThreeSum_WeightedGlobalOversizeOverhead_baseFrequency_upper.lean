-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_baseFrequency_upper
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.baseFrequency_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:03:39.848114+00:00
-- url     : https://prove2.me/theorems/9703ef37-c72e-4282-abe4-0508516d2f32
-- title:
--   Weighted Global Oversize Overhead: base Frequency upper
-- statement:
--   The Weighted Global Oversize Overhead construction uses the base Frequency upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L88-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L88-L100

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.baseFrequency_upper {K : ℕ} (hK : 0 < K) (m : ℕ) :
    baseFrequency K m ≤ 2^361*(m+1)^7 := by sorry
