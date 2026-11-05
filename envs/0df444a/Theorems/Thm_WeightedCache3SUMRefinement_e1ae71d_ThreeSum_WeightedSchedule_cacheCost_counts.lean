-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_cacheCost_counts
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.cacheCost_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:14.959475+00:00
-- url     : https://prove2.me/theorems/95958906-8a5b-4d7c-82be-86081f6f1ff8
-- title:
--   cacheCost_counts
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean#L35-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean#L35-L42

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.cacheCost_counts {N : ℕ} (Q : TritWord N) :
    cacheCost Q=1369*digitCount Q 1+2740*digitCount Q 2 := by sorry
