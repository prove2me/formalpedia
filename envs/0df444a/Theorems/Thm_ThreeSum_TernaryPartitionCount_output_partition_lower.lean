-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_output_partition_lower
-- name    : ThreeSum.TernaryPartitionCount.output_partition_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:16.474055+00:00
-- url     : https://prove2.me/theorems/566fc0a7-cbd4-435e-a33a-4cb1f3e6130d
-- title:
--   Ternary Partition Count: output partition lower
-- statement:
--   Every genuine fixed-type output has at least the full balanced binary
--   and balanced ternary partition product.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L198-L212
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L198-L212

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

theorem ThreeSum.TernaryPartitionCount.output_partition_lower (t r s : ℕ) (q : TritWord (t+2*r+3*s))
    (hq : HasType q (piType t r s)) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) q) := by sorry
