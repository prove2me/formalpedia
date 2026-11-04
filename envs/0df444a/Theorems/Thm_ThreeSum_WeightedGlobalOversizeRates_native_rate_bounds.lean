-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_native_rate_bounds
-- name    : ThreeSum.WeightedGlobalOversizeRates.native_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:24.225768+00:00
-- url     : https://prove2.me/theorems/7d64117e-15d2-4cf3-bea6-a7215c325dbf
-- title:
--   Weighted Global Oversize Rates: native rate bounds
-- statement:
--   The Weighted Global Oversize Rates construction uses the native rate bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L67-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L67-L98

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeRates.native_rate_bounds {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    (outputRate m+partitionEntropy)/2+inflationRate K m ≤ nativeRate K m ∧
    nativeRate K m ≤ (outputRate m+partitionEntropy)/2+inflationRate K m+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by sorry
