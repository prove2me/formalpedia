-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_output_partition_lower
-- name    : ThreeSum.WeightedGlobalPartitionCount.output_partition_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:27.10022+00:00
-- url     : https://prove2.me/theorems/c77c4979-7f91-4aa5-9617-ae51df61d7d9
-- title:
--   Weighted Global Partition Count: output partition lower
-- statement:
--   Every genuine fixed-type output has at least the full balanced binary
--   and balanced ternary partition product.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L205-L219
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L205-L219

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalPartitionCount.output_partition_lower (t r s : ℕ) (q : TritWord (t+2*r+3*s))
    (hq : HasType q (piType t r s)) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) q) := by sorry
