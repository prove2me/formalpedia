-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_lift_tensor
-- name    : ThreeSum.LightWeightedGlobalSeedScore.lift_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:24:35.5112+00:00
-- url     : https://prove2.me/theorems/484ea081-3f18-4536-977f-b964a138f81e
-- title:
--   Light Weighted Global Seed Score: lift tensor
-- statement:
--   The Light Weighted Global Seed Score construction uses the lift tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L183-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L183-L188

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
variable {lim : Limits} {entry depth T : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
  {Post : ℤ → (ℕ → ℤ) → Prop}

theorem ThreeSum.LightWeightedGlobalSeedScore.lift_tensor (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim (LightWeightedGlobalTensorDriver.program xl yl zl xr yr zr K) entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (25+entry) depth vals μ T Post := by sorry
