-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_row
-- name    : ThreeSum.TernaryMomentSchedule.aggregate_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:42.493746+00:00
-- url     : https://prove2.me/theorems/84010d56-d48d-488c-9a01-b60e366e1e39
-- title:
--   Ternary Moment Schedule: aggregate row
-- statement:
--   The Ternary Moment Schedule construction uses the aggregate row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L30-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L30-L39

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.aggregate_row (score : ℕ→ℕ→ℕ→ℤ) (l k i : ℕ) :
    aggregate (row l) score k i=
      if l=k then ∑ j∈range (l+1), score l j i else 0 := by sorry
