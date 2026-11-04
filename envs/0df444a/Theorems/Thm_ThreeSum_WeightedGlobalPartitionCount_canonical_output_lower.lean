-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_canonical_output_lower
-- name    : ThreeSum.WeightedGlobalPartitionCount.canonical_output_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:07.890198+00:00
-- url     : https://prove2.me/theorems/f0c9c6cd-6e7d-42ed-ad4c-3db5ea2a3436
-- title:
--   Weighted Global Partition Count: canonical output lower
-- statement:
--   The Weighted Global Partition Count construction uses the canonical output lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L187-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L187-L201

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

theorem ThreeSum.WeightedGlobalPartitionCount.canonical_output_lower (t r s : ℕ) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s)) := by sorry
