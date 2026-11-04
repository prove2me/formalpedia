-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_selectedMoment_pos
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.selectedMoment_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:03:36.482305+00:00
-- url     : https://prove2.me/theorems/add0812a-9c0f-484c-b578-07ceb415db38
-- title:
--   Weighted Global Oversize Overhead: selected Moment pos
-- statement:
--   The Weighted Global Oversize Overhead construction uses the selected Moment pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L189-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L189-L191

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.selectedMoment_pos {K : ℕ} (hK : 0 < K) : 0 < selectedMoment K := by sorry
