-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedFamilyMargin_simultaneous_parameters
-- name    : ThreeSum.WeightedGlobalPairedFamilyMargin.simultaneous_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:13:20.945491+00:00
-- url     : https://prove2.me/theorems/a778680a-f4b0-4f1d-a59a-2cd5d06173c1
-- title:
--   Weighted Global Paired Family Margin: simultaneous parameters
-- statement:
--   One fixed native block satisfies the exact paired drift guard together
--   with the original signed preprocessing and all principal exponent margins.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedFamilyMargin.lean#L112-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedFamilyMargin.lean#L112-L124

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedFamilyMargin
open Filter Real WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalPairedFamilyMargin.simultaneous_parameters {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      WeightedGlobalSignedPadding.carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m := by sorry
