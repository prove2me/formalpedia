-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_canonical_output_lower
-- name    : ThreeSum.TernaryPartitionCount.canonical_output_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:18.369868+00:00
-- url     : https://prove2.me/theorems/15624d43-9c06-4739-b59f-8f7b38881645
-- title:
--   Ternary Partition Count: canonical output lower
-- statement:
--   The Ternary Partition Count construction uses the canonical output lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L180-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L180-L194

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

theorem ThreeSum.TernaryPartitionCount.canonical_output_lower (t r s : ℕ) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s)) := by sorry
