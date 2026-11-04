-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_gt_four
-- name    : ThreeSum.WeightedGlobalOversizePrime.nativePrime_gt_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:49.81347+00:00
-- url     : https://prove2.me/theorems/19f08273-a582-4177-8913-d7d682cd6c98
-- title:
--   Weighted Global Oversize Prime: native Prime gt four
-- statement:
--   The Weighted Global Oversize Prime construction uses the native Prime gt four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L126-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L126-L134

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

theorem ThreeSum.WeightedGlobalOversizePrime.nativePrime_gt_four {K m : ℕ} (hK : 0 < K) (hm : 0 < m) : 4 < nativePrime K m := by sorry
