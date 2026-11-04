-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_length_le
-- name    : ThreeSum.TernaryMomentSchedule.length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:07.687218+00:00
-- url     : https://prove2.me/theorems/99ceb06e-57f5-48f6-93a6-6b5e1bfae72f
-- title:
--   Ternary Moment Schedule: length le
-- statement:
--   The Ternary Moment Schedule construction uses the length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L74-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L74-L79

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.length_le (terms : ℕ) : (channels terms).length≤terms^2 := by sorry
