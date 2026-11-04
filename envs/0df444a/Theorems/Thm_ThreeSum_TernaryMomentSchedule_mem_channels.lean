-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_mem_channels
-- name    : ThreeSum.TernaryMomentSchedule.mem_channels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:50.28721+00:00
-- url     : https://prove2.me/theorems/fab73848-fa41-4704-a9c2-c4096c6a0d1b
-- title:
--   Ternary Moment Schedule: mem channels
-- statement:
--   The Ternary Moment Schedule construction uses the mem channels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L57-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L57-L72

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.mem_channels {terms k j : ℕ} :
    (k,j)∈channels terms ↔ k<terms ∧ j≤k := by sorry
