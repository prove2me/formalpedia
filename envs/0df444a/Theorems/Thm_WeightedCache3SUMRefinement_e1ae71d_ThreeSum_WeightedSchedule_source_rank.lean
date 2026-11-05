-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_source_rank
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.source_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:08.439751+00:00
-- url     : https://prove2.me/theorems/fc350b35-d93c-48ae-b855-a08246d62d91
-- title:
--   source_rank
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean#L57-L60

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.source_rank {m : ℕ} {A : TritWord (fixedLength m)}
    (hA : HasType A (fixedAlpha m)) : TernaryBank.rank A=sourceRank m := by sorry
