-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_base_lower
-- name    : ThreeSum.WeightedGlobalOversizePrime.nativePrime_base_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:41:39.940795+00:00
-- url     : https://prove2.me/theorems/b8447c65-9faf-41d4-84d2-3c1678aefde5
-- title:
--   Weighted Global Oversize Prime: native Prime base lower
-- statement:
--   The Weighted Global Oversize Prime construction uses the native Prime base lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L119-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L119-L124

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

theorem ThreeSum.WeightedGlobalOversizePrime.nativePrime_base_lower {K : ℕ} (hK : 0 < K) (m : ℕ) :
    threshold m ≤ nativePrime K m^2 := by sorry
