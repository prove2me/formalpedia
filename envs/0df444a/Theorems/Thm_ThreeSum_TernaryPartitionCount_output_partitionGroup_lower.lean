-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_output_partitionGroup_lower
-- name    : ThreeSum.TernaryPartitionCount.output_partitionGroup_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:22.11538+00:00
-- url     : https://prove2.me/theorems/e3caac15-ece7-47f8-b4d2-d3045eb6430b
-- title:
--   Ternary Partition Count: output partition Group lower
-- statement:
--   The Ternary Partition Count construction uses the output partition Group lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L218-L224
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L218-L224

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

theorem ThreeSum.TernaryPartitionCount.output_partitionGroup_lower (t r s : ℕ) (q : TritWord (t+2*r+3*s))
    (hq : HasType q (piType t r s)) :
    partitionGroup r s ≤ Fintype.card (outputFiber (alphaType t r s) (piType t r s) q) := by sorry
