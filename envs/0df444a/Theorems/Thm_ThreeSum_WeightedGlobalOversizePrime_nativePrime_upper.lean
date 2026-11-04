-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_upper
-- name    : ThreeSum.WeightedGlobalOversizePrime.nativePrime_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:32.251579+00:00
-- url     : https://prove2.me/theorems/247c38d4-fd97-49a7-b929-578b859abe8d
-- title:
--   Weighted Global Oversize Prime: native Prime upper
-- statement:
--   The Weighted Global Oversize Prime construction uses the native Prime upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L114-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L114-L117

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

theorem ThreeSum.WeightedGlobalOversizePrime.nativePrime_upper {K : ℕ} (hK : 0 < K) (m : ℕ) :
    nativePrime K m^2 ≤ 16*inflatedThreshold K m := by sorry
