-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColoredSolver_arenaArgs_length
-- name    : ThreeSum.LightWeightedGlobalColoredSolver.arenaArgs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:46:07.638231+00:00
-- url     : https://prove2.me/theorems/def71aff-0d5c-4262-b3dc-10417b3c1825
-- title:
--   Light Weighted Global Colored Solver: arena Args length
-- statement:
--   The Light Weighted Global Colored Solver construction uses the arena Args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L60-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L60-L60

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

theorem ThreeSum.LightWeightedGlobalColoredSolver.arenaArgs_length (p R F : ℕ) : (arenaArgs p R F).length=23 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColoredSolver.arenaArgs_length
