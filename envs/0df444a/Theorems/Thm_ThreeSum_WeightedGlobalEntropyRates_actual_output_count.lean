-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_count
-- name    : ThreeSum.WeightedGlobalEntropyRates.actual_output_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:02.666274+00:00
-- url     : https://prove2.me/theorems/888ead5b-48c1-4cdf-bce8-d399d98cbcdc
-- title:
--   Weighted Global Entropy Rates: actual output count
-- statement:
--   The Weighted Global Entropy Rates construction uses the actual output count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L96-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L96-L102

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

theorem ThreeSum.WeightedGlobalEntropyRates.actual_output_count (m : ℕ) :
    outputSize m=typeCount 30000000000000 4760008248000 878239641000 m := by sorry
