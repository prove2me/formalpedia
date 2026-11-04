-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualRuntimeParameters_simultaneous_parameters
-- name    : ThreeSum.WeightedGlobalActualRuntimeParameters.simultaneous_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:27:31.223542+00:00
-- url     : https://prove2.me/theorems/bc3f2711-8175-42a8-b2eb-56ad4fa76e56
-- title:
--   Weighted Global Actual Runtime Parameters: simultaneous parameters
-- statement:
--   The digit radix and one sufficiently large fixed ternary block meet
--   both the exact minor guard and the complete runtime exponent budget.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualRuntimeParameters.lean#L36-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualRuntimeParameters.lean#L36-L47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_simultaneous_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalPairedFamilyMargin_simultaneous_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualRuntimeParameters
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalOversizePrime
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalSignedPadding
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalActualRuntimeParameters.simultaneous_parameters {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      fullExponent K (selectedMoment K) c d m+microAllowance K+(1/1250000000:ℝ)<
        WeightedGlobalParameters.targetExponent:= by sorry
