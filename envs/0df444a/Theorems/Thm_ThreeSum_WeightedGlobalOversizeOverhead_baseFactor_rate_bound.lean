-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_baseFactor_rate_bound
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.baseFactor_rate_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:02.962511+00:00
-- url     : https://prove2.me/theorems/46f589bd-69ae-4266-a21d-01b20cfdafbf
-- title:
--   Weighted Global Oversize Overhead: base Factor rate bound
-- statement:
--   The Weighted Global Oversize Overhead construction uses the base Factor rate bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L114-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L114-L156

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.baseFactor_rate_bound {K k m : ℕ} (hK : 0 < K) (hk : 0 < k) (hm : 0 < m) (c d : ℕ) :
    Real.log (baseFactor K k c d m : ℝ)/((fixedLength m : ℝ)*Real.log 2) ≤ rateUpper k c d m := by sorry
