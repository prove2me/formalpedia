-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColoredSolver_postArgs_length
-- name    : ThreeSum.LightWeightedGlobalColoredSolver.postArgs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:47:10.036544+00:00
-- url     : https://prove2.me/theorems/b0cc431b-9881-4fe6-a49d-6734fdd1b0f7
-- title:
--   Light Weighted Global Colored Solver: post Args length
-- statement:
--   The Light Weighted Global Colored Solver construction uses the post Args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L63-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L63-L63

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalColoredSolver
open Light
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

theorem ThreeSum.LightWeightedGlobalColoredSolver.postArgs_length : postArgs.length=148 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColoredSolver.postArgs_length
