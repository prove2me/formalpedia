-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColoredSolver_libraries_length
-- name    : ThreeSum.LightWeightedGlobalColoredSolver.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:40:43.95872+00:00
-- url     : https://prove2.me/theorems/c3511514-9521-43ef-931b-1e7d5b7afb15
-- title:
--   Light Weighted Global Colored Solver: libraries length
-- statement:
--   The Light Weighted Global Colored Solver construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L88-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColoredSolver.lean#L88-L91

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalColoredSolver
open Light
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

theorem ThreeSum.LightWeightedGlobalColoredSolver.libraries_length (radix D E K bDigit a b scaleBase p R F : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) :
    (libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr).length=252 := by sorry
