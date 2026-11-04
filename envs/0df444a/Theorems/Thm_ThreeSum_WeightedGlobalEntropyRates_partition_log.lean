-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_partition_log
-- name    : ThreeSum.WeightedGlobalEntropyRates.partition_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:22.383264+00:00
-- url     : https://prove2.me/theorems/c43016c0-7766-418c-9241-ff00dc6b6ce0
-- title:
--   Weighted Global Entropy Rates: partition log
-- statement:
--   The Weighted Global Entropy Rates construction uses the partition log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L125-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L125-L134

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

theorem ThreeSum.WeightedGlobalEntropyRates.partition_log (m : ℕ) : Real.log (partitionCap m : ℝ)=
    (fixedLength m : ℝ)*Real.log 2*WeightedGlobalParameters.partitionEntropy := by sorry
