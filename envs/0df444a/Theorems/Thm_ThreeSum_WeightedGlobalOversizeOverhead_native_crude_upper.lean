-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_native_crude_upper
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.native_crude_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:03:16.631883+00:00
-- url     : https://prove2.me/theorems/e5be10ac-54dd-4ab8-8f3f-4c369a12b614
-- title:
--   Weighted Global Oversize Overhead: native crude upper
-- statement:
--   The Weighted Global Oversize Overhead construction uses the native crude upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L20-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L20-L38

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.native_crude_upper {K : ℕ} (hK : 0 < K) (m : ℕ) :
    nativePrime K m ≤ 2^(4*fixedLength m+2) := by sorry
