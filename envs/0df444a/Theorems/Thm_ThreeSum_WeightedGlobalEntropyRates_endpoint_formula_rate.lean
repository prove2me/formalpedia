-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_endpoint_formula_rate
-- name    : ThreeSum.WeightedGlobalEntropyRates.endpoint_formula_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:39.101744+00:00
-- url     : https://prove2.me/theorems/4a98548d-f4c3-42d0-acfa-e84dc8d5b162
-- title:
--   Weighted Global Entropy Rates: endpoint formula rate
-- statement:
--   The Weighted Global Entropy Rates construction uses the endpoint formula rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L85-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L85-L90

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

theorem ThreeSum.WeightedGlobalEntropyRates.endpoint_formula_rate :
    Tendsto (fun m : ℕ => Real.log (typeCount 30000000000000 2672750671000 292746547000 m : ℝ)/
      (((30000000000000*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 WeightedGlobalParameters.Halpha) := by sorry
