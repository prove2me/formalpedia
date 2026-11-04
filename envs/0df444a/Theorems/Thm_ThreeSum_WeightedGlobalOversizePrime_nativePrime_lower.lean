-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_lower
-- name    : ThreeSum.WeightedGlobalOversizePrime.nativePrime_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:15.101921+00:00
-- url     : https://prove2.me/theorems/0080d4ec-73a5-4066-b340-bdf72bd57d8c
-- title:
--   Weighted Global Oversize Prime: native Prime lower
-- statement:
--   The Weighted Global Oversize Prime construction uses the native Prime lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L111-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L111-L113

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

theorem ThreeSum.WeightedGlobalOversizePrime.nativePrime_lower (K m : ℕ) : inflatedThreshold K m ≤ nativePrime K m^2 := by sorry
