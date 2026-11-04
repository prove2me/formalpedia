-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColoredSolver_loopArgs_length
-- name    : ThreeSum.LightWeightedGlobalColoredSolver.loopArgs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:51:39.47201+00:00
-- url     : https://prove2.me/theorems/a39e9786-9b6f-41a3-b889-9481813a0b61
-- title:
--   Light Weighted Global Colored Solver: loop Args length
-- statement:
--   The Light Weighted Global Colored Solver construction uses the loop Args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L61-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L61-L62

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

theorem ThreeSum.LightWeightedGlobalColoredSolver.loopArgs_length (m F p alpha2 alphaRank localQ R a b scaleBase : ℕ) :
    (loopArgs m F p alpha2 alphaRank localQ R a b scaleBase).length=17 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColoredSolver.loopArgs_length
