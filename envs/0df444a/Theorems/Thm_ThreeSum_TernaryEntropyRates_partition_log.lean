-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_partition_log
-- name    : ThreeSum.TernaryEntropyRates.partition_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:51.798409+00:00
-- url     : https://prove2.me/theorems/cbefc63a-15ba-4b3e-ba49-47e0890085ad
-- title:
--   Ternary Entropy Rates: partition log
-- statement:
--   The Ternary Entropy Rates construction uses the partition log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L118-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L118-L128

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.TernaryEntropyRates.partition_log (m : ℕ) : Real.log (partitionCap m : ℝ)=
    (fixedLength m : ℝ)*Real.log 2*TernaryParameters.partitionEntropy := by sorry
