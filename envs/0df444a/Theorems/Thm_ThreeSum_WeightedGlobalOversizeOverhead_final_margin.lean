-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_final_margin
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.final_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:40.388993+00:00
-- url     : https://prove2.me/theorems/746f8eec-2359-420a-8187-41f1853acd93
-- title:
--   Weighted Global Oversize Overhead: final margin
-- statement:
--   The Weighted Global Oversize Overhead construction uses the final margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L263-L272
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L263-L272

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.final_margin {K : ℕ} (hK : 100000000000000000000 ≤ K) :
    softCertificate+microAllowance K < targetExponent := by sorry
