-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationCall_indexed_witness
-- name    : ThreeSum.WeightedGlobalColoredPreparationCall.indexed_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:29:57.850054+00:00
-- url     : https://prove2.me/theorems/0d85dca0-b8cf-4660-917d-3f80da40df2e
-- title:
--   Weighted Global Colored Preparation Call: indexed witness
-- statement:
--   The Weighted Global Colored Preparation Call construction uses the indexed witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L75-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L75-L90

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

theorem ThreeSum.WeightedGlobalColoredPreparationCall.indexed_witness (A B C : List ℤ) :
    (∃i<A.length,∃j<B.length,∃k<C.length,C.getD k 0=A.getD i 0+B.getD j 0)↔
      LightTernaryColorPrelude.witness A B C := by sorry
