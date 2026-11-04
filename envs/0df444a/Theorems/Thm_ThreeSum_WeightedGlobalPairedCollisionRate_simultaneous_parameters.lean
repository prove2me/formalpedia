-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_simultaneous_parameters
-- name    : ThreeSum.WeightedGlobalPairedCollisionRate.simultaneous_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:28:58.316957+00:00
-- url     : https://prove2.me/theorems/713e8174-1581-4844-b11d-6320e0e7bb8e
-- title:
--   Weighted Global Paired Collision Rate: simultaneous parameters
-- statement:
--   All exact paired, collision, preprocessing and principal cost margins
--   hold in one fixed block, chosen before inspecting the input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L103-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L103-L121

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_WeightedGlobalPairedFamilyMargin_simultaneous_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalPairedCollisionRate.simultaneous_parameters {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      WeightedGlobalOversizeOverhead.overheadCharge (WeightedGlobalOversizeOverhead.selectedMoment K) c d m<
        WeightedGlobalOversizeOverhead.microAllowance K ∧
      WeightedGlobalSignedPadding.carryExponent m (2^t) κ<WeightedGlobalOversizeOverhead.microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*(nativeFamily K m (WeightedGlobalOversizeOverhead.selectedMoment K)).length)^4≤outputSize m ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) := by sorry
