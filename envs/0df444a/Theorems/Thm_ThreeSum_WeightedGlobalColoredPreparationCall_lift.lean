-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationCall_lift
-- name    : ThreeSum.WeightedGlobalColoredPreparationCall.lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:31:04.962043+00:00
-- url     : https://prove2.me/theorems/63f1a604-e3c3-4d1b-9f25-e048d7e408f1
-- title:
--   Weighted Global Colored Preparation Call: lift
-- statement:
--   The original-input preparation executes as the literal first library
--   of the full per-color executable.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L19-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L19-L39

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

theorem ThreeSum.WeightedGlobalColoredPreparationCall.lift {lim : Limits} {radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) {entry depth T : ℕ} {args : List ℤ}
    {μ : ℕ→ℤ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (h : Meets lim (LightWeightedGlobalColorPreparation.program radix) entry depth args μ T Q) :
    Meets lim (program radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L
      raws words maps xl yl zl xr yr zr post postMain) entry depth args μ T Q := by sorry
