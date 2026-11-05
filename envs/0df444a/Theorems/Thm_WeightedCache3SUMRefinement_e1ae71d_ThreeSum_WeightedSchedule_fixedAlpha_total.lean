-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_fixedAlpha_total
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.fixedAlpha_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:14.745567+00:00
-- url     : https://prove2.me/theorems/192a47be-e9e5-42b3-9a11-969ae1521031
-- title:
--   fixedAlpha_total
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean#L24-L25

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.fixedAlpha_total (m : ℕ) : ∑ d : Fin 3, fixedAlpha m d = fixedLength m := by sorry
