-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
-- name    : ThreeSum.WeightedGlobalEntropyRates.actual_output_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:05.81098+00:00
-- url     : https://prove2.me/theorems/80451262-9d56-4a51-961d-ef9557b8b617
-- title:
--   Weighted Global Entropy Rates: actual output rate
-- statement:
--   The Weighted Global Entropy Rates construction uses the actual output rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L118-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L118-L120

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

theorem ThreeSum.WeightedGlobalEntropyRates.actual_output_rate : Tendsto outputRate atTop (𝓝 WeightedGlobalParameters.Hpi) := by sorry
