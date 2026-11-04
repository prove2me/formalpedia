-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_canonicalEdge_injective
-- name    : ThreeSum.TernaryPartitionCount.canonicalEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:17.481423+00:00
-- url     : https://prove2.me/theorems/7b13daeb-b5ae-4785-b947-a3a5b15ca521
-- title:
--   Ternary Partition Count: canonical Edge injective
-- statement:
--   The Ternary Partition Count construction uses the canonical Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L172-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L172-L178

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

theorem ThreeSum.TernaryPartitionCount.canonicalEdge_injective {t r s : ℕ} :
    Function.Injective (canonicalEdge (t := t) (r := r) (s := s)) := by sorry
