-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_canonicalEdge_injective
-- name    : ThreeSum.WeightedGlobalPartitionCount.canonicalEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:11.126543+00:00
-- url     : https://prove2.me/theorems/93b9788c-5c29-4ee5-8982-90fb3968a627
-- title:
--   Weighted Global Partition Count: canonical Edge injective
-- statement:
--   The Weighted Global Partition Count construction uses the canonical Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L179-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L179-L185

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

theorem ThreeSum.WeightedGlobalPartitionCount.canonicalEdge_injective {t r s : ℕ} :
    Function.Injective (canonicalEdge (t := t) (r := r) (s := s)) := by sorry
