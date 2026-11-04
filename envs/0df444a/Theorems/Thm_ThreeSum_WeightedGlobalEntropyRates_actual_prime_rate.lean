-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_prime_rate
-- name    : ThreeSum.WeightedGlobalEntropyRates.actual_prime_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:54.12712+00:00
-- url     : https://prove2.me/theorems/c38f92de-6bee-4423-b696-fd1983d6c0d0
-- title:
--   Weighted Global Entropy Rates: actual prime rate
-- statement:
--   The Weighted Global Entropy Rates construction uses the actual prime rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L185-L196
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L185-L196

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

theorem ThreeSum.WeightedGlobalEntropyRates.actual_prime_rate :
    Tendsto primeRate atTop (𝓝 ((WeightedGlobalParameters.Hpi+WeightedGlobalParameters.partitionEntropy)/2)) := by sorry
