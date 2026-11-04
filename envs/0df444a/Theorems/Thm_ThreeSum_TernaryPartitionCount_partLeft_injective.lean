-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_partLeft_injective
-- name    : ThreeSum.TernaryPartitionCount.partLeft_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:51.613202+00:00
-- url     : https://prove2.me/theorems/e4409a25-1f55-444d-9185-a98d8810ee70
-- title:
--   Ternary Partition Count: part Left injective
-- statement:
--   The Ternary Partition Count construction uses the part Left injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L102-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L102-L122

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

theorem ThreeSum.TernaryPartitionCount.partLeft_injective {t r s : ℕ} : Function.Injective (partLeft (t := t) (r := r) (s := s)) := by sorry
