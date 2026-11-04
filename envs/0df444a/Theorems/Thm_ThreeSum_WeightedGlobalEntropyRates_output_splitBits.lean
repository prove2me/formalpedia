-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_output_splitBits
-- name    : ThreeSum.WeightedGlobalEntropyRates.output_splitBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:29.732127+00:00
-- url     : https://prove2.me/theorems/caa1aa16-b84c-4e2e-8451-71f66e7df8bd
-- title:
--   Weighted Global Entropy Rates: output split Bits
-- statement:
--   The Weighted Global Entropy Rates construction uses the output split Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L64-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L64-L69

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

theorem ThreeSum.WeightedGlobalEntropyRates.output_splitBits : splitBits 30000000000000 4760008248000 878239641000 = WeightedGlobalParameters.Hpi := by sorry
