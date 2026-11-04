-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_partLeft_injective
-- name    : ThreeSum.WeightedGlobalPartitionCount.partLeft_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:19.86082+00:00
-- url     : https://prove2.me/theorems/ccfbedb2-a7a3-4e85-97af-b196dff00aef
-- title:
--   Weighted Global Partition Count: part Left injective
-- statement:
--   The Weighted Global Partition Count construction uses the part Left injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L109-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L109-L129

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

theorem ThreeSum.WeightedGlobalPartitionCount.partLeft_injective {t r s : ℕ} : Function.Injective (partLeft (t := t) (r := r) (s := s)) := by sorry
