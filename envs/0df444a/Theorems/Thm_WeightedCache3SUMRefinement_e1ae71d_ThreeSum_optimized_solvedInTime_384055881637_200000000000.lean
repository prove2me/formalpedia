-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_optimized_solvedInTime_384055881637_200000000000
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.optimized_solvedInTime_384055881637_200000000000
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:12:54.369104+00:00
-- url     : https://prove2.me/theorems/8daa5e55-d689-46cf-8aaf-4e9e926c49e4
-- title:
--   optimized_solvedInTime_384055881637_200000000000
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFinalSolver.lean#L22-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFinalSolver.lean#L22-L28

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileFastExecution
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFinalSolver
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
open Light WeightedGlobalConcreteProfile

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.optimized_solvedInTime_384055881637_200000000000 :
    EndStatement.ThreeSum.SolvedInTime (384055881637/200000000000 : Rat) := by sorry
