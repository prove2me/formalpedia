-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters
-- name    : ThreeSum.WeightedGlobalSignedParameters.simultaneous_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:15:40.830961+00:00
-- url     : https://prove2.me/theorems/385e195a-b367-493a-ac3d-511bdf54562e
-- title:
--   Weighted Global Signed Parameters: simultaneous parameters
-- statement:
--   The base is fixed first. The block is then chosen far enough out for
--   all principal charges, repeated local losses, padding, and original-row
--   integer-minor preservation to hold simultaneously.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedParameters.lean#L76-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedParameters.lean#L76-L100

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology

theorem ThreeSum.WeightedGlobalSignedParameters.simultaneous_parameters {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m := by sorry
