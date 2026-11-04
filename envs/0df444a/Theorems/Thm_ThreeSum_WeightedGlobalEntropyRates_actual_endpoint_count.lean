-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_endpoint_count
-- name    : ThreeSum.WeightedGlobalEntropyRates.actual_endpoint_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:45.556682+00:00
-- url     : https://prove2.me/theorems/934a1c51-0e54-47ac-8b00-af895905e808
-- title:
--   Weighted Global Entropy Rates: actual endpoint count
-- statement:
--   The Weighted Global Entropy Rates construction uses the actual endpoint count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L105-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L105-L111

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

theorem ThreeSum.WeightedGlobalEntropyRates.actual_endpoint_count (m : ℕ) :
    endpointSize m=typeCount 30000000000000 2672750671000 292746547000 m := by sorry
