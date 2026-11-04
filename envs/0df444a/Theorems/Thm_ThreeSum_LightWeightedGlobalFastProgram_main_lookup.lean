-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalFastProgram_main_lookup
-- name    : ThreeSum.LightWeightedGlobalFastProgram.main_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:42:19.186328+00:00
-- url     : https://prove2.me/theorems/c12e6d9e-67be-4ef1-b5e7-2f5f21935d6d
-- title:
--   Light Weighted Global Fast Program: main lookup
-- statement:
--   The Light Weighted Global Fast Program construction uses the main lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryFastProgram.lean#L80-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryFastProgram.lean#L80-L85

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgram
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalFastProgram
open Light
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalFastProgram.main_lookup (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    (program M radix p K κ color colorMain)[mainEntry color]?=some (body (hostEntry color)) := by sorry
