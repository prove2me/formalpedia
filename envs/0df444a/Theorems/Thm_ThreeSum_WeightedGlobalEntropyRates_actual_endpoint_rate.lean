-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_endpoint_rate
-- name    : ThreeSum.WeightedGlobalEntropyRates.actual_endpoint_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:02.474865+00:00
-- url     : https://prove2.me/theorems/15f938bf-ea15-446d-9779-d1c845bd6590
-- title:
--   Weighted Global Entropy Rates: actual endpoint rate
-- statement:
--   The Weighted Global Entropy Rates construction uses the actual endpoint rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L121-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L121-L123

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

theorem ThreeSum.WeightedGlobalEntropyRates.actual_endpoint_rate : Tendsto endpointRate atTop (𝓝 WeightedGlobalParameters.Halpha) := by sorry
