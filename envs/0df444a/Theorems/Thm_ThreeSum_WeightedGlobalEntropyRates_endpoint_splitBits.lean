-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_endpoint_splitBits
-- name    : ThreeSum.WeightedGlobalEntropyRates.endpoint_splitBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:26.821727+00:00
-- url     : https://prove2.me/theorems/3860114e-6617-4fa0-a702-cb4e00f317ee
-- title:
--   Weighted Global Entropy Rates: endpoint split Bits
-- statement:
--   The Weighted Global Entropy Rates construction uses the endpoint split Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L71-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L71-L76

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

theorem ThreeSum.WeightedGlobalEntropyRates.endpoint_splitBits : splitBits 30000000000000 2672750671000 292746547000 = WeightedGlobalParameters.Halpha := by sorry
