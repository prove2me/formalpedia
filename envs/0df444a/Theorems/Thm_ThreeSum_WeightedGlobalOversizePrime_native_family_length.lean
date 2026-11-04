-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_native_family_length
-- name    : ThreeSum.WeightedGlobalOversizePrime.native_family_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:43.056042+00:00
-- url     : https://prove2.me/theorems/3e4cd2e7-7a4f-4cdd-8afc-8c7c3b200519
-- title:
--   Weighted Global Oversize Prime: native family length
-- statement:
--   The Weighted Global Oversize Prime construction uses the native family length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L182-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L182-L184

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalOversizePrime.native_family_length (K m k : ℕ) :
    (nativeFamily K m k).length=inflatedFrequency K m*(Nat.log2 (nativePrime K m^2)+1) := by sorry
