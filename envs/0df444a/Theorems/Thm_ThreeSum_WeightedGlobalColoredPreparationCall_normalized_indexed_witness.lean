-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationCall_normalized_indexed_witness
-- name    : ThreeSum.WeightedGlobalColoredPreparationCall.normalized_indexed_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:30:09.443708+00:00
-- url     : https://prove2.me/theorems/2a02c3c2-b5cf-4a98-810f-78052b55c1db
-- title:
--   Weighted Global Colored Preparation Call: normalized indexed witness
-- statement:
--   The Weighted Global Colored Preparation Call construction uses the normalized indexed witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L92-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L92-L100

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationCall
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPreparationCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalColoredPreparationCall.normalized_indexed_witness {n : ℕ}
    {p : Coloring.Parameter (LightColorParametersCosts.width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : LightTernaryColorPrelude.Normalized μ ab n (ColorClassLists.classList p x 0 1) A)
    (hB : LightTernaryColorPrelude.Normalized μ bb n (ColorClassLists.classList p x 1 1) B)
    (hC : LightTernaryColorPrelude.Normalized μ cb n (ColorClassLists.classList p x 2 (-1)) C) :
    (∃i<A.length,∃j<B.length,∃k<C.length,C.getD k 0=A.getD i 0+B.getD j 0)↔
      ColorClassLists.witness p x := by sorry
