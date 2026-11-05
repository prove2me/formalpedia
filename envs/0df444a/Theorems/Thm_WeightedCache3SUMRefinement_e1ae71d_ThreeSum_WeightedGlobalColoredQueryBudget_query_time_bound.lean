-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredQueryBudget_query_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget.query_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:21.948331+00:00
-- url     : https://prove2.me/theorems/1419efba-6ba0-441f-85e3-503a47dd4e13
-- title:
--   query_time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredQueryBudget.lean#L24-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredQueryBudget.lean#L24-L48

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredQueryBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget.query_time_bound (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hn : 1<n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    (queryTime P n free A B C:ℝ)≤
      (coefficient P:ℝ)*(J P n+1:ℕ)^3*
        WeightedGlobalCountFrontendBudget.envelope P.m (rounds P n) := by sorry
