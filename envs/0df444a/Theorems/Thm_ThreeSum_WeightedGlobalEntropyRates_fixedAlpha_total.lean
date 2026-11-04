-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_fixedAlpha_total
-- name    : ThreeSum.WeightedGlobalEntropyRates.fixedAlpha_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:40.882814+00:00
-- url     : https://prove2.me/theorems/0655790a-97b0-4036-ad11-80b8c46c0835
-- title:
--   Weighted Global Entropy Rates: fixed Alpha total
-- statement:
--   The Weighted Global Entropy Rates construction uses the fixed Alpha total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L92-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L92-L94

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.WeightedGlobalEntropyRates.fixedAlpha_total (m : ℕ) : fixedAlpha m 0+fixedAlpha m 1+fixedAlpha m 2=fixedLength m := by sorry
