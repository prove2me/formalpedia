-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_base_factor_eventually
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.base_factor_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:24.765197+00:00
-- url     : https://prove2.me/theorems/82db5a2b-2d1f-4306-8cb2-2fe1d115a5f6
-- title:
--   Weighted Global Oversize Overhead: base factor eventually
-- statement:
--   This is the actual repeated polynomial-carry, noninflation-family and
--   raw-cap factor, with its fixed prefactor absorbed by the strict margin.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L245-L253
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L245-L253

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.base_factor_eventually {K k m : ℕ} (hK : 0 < K) (hk : 0 < k) (hm : 0 < m)
    (c d : ℕ) {ε : ℝ} (he : overheadCharge k c d m < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((baseFactor K k c d m)^(radixLength m n) : ℝ) ≤ (n : ℝ)^ε := by sorry
