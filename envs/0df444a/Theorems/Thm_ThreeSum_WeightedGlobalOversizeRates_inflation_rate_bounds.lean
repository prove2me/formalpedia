-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_inflation_rate_bounds
-- name    : ThreeSum.WeightedGlobalOversizeRates.inflation_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:07.34695+00:00
-- url     : https://prove2.me/theorems/aac6c5d1-3a0a-4482-bfb2-ce0bd39e86c6
-- title:
--   Weighted Global Oversize Rates: inflation rate bounds
-- statement:
--   The Weighted Global Oversize Rates construction uses the inflation rate bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L31-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean#L31-L54

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

theorem ThreeSum.WeightedGlobalOversizeRates.inflation_rate_bounds {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    outputRate m/K ≤ inflationRate K m ∧
      inflationRate K m ≤ outputRate m/K+Real.log 2/((fixedLength m : ℝ)*Real.log 2) := by sorry
