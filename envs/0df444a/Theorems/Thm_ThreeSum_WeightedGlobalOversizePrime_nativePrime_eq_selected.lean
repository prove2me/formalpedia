-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_eq_selected
-- name    : ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:35.76284+00:00
-- url     : https://prove2.me/theorems/14944907-92b1-45e3-b96b-926ef14a9d97
-- title:
--   Weighted Global Oversize Prime: native Prime eq selected
-- statement:
--   The Weighted Global Oversize Prime construction uses the native Prime eq selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L96-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L96-L98

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
attribute [local semireducible] nativePrime

theorem ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected (K m : ℕ) :
    nativePrime K m=LocalCoverBounds.selectedPrime (inflatedThreshold K m) := by sorry
