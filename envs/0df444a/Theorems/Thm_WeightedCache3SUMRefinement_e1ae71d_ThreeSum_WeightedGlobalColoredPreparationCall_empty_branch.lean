-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPreparationCall_empty_branch
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall.empty_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:56:49.354224+00:00
-- url     : https://prove2.me/theorems/738a4147-8014-496d-bdc7-fbec7587a962
-- title:
--   empty_branch
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L104-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L104-L120

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationCall
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall.empty_branch {lim : Limits} {P : Program} {d n free U R J q menu radix : ℕ}
    {p : Coloring.Parameter (LightColorParametersCosts.width n)} {x : Fin n→ℤ}
    (loc μ ν : ℕ→ℤ) (tail : Stmt)
    (hout : LightWeightedGlobalColorPreparationProof.Output μ ν free U R J q menu radix p x 0)
    (hzero : loc 5=0) (hw : (0:ℤ)≤lim.word) :
    Ends lim P d (.ite (v 5 =' k 0) (.set 0 (k 0)) tail) ⟨loc,ν⟩ 100
      (fun σ=>σ.loc 0=0 ∧ ¬ColorClassLists.witness p x ∧ Kept μ σ.mem free) := by sorry
