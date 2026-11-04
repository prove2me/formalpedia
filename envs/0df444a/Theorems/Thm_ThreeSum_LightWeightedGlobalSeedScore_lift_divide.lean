-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_lift_divide
-- name    : ThreeSum.LightWeightedGlobalSeedScore.lift_divide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:24:41.131091+00:00
-- url     : https://prove2.me/theorems/e8b78159-dc42-4a57-af25-44c79f6a8ed6
-- title:
--   Light Weighted Global Seed Score: lift divide
-- statement:
--   The Light Weighted Global Seed Score construction uses the lift divide property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L173-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L173-L181

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

theorem ThreeSum.LightWeightedGlobalSeedScore.lift_divide (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim LightSmallDivide.program entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (24+entry) depth vals μ T Post := by sorry
