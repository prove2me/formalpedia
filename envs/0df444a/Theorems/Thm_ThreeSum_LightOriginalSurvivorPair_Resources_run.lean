-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_Resources_run
-- name    : ThreeSum.LightOriginalSurvivorPair.Resources.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:55:29.634542+00:00
-- url     : https://prove2.me/theorems/e7beba90-8c94-4ebf-9100-38f803d78d19
-- title:
--   Resources: run
-- statement:
--   The Resources construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorResources.lean#L81-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorResources.lean#L81-L93

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress LightOriginalCollisionCleanup

theorem ThreeSum.LightOriginalSurvivorPair.Resources.run {c : Layout} {lim : Limits} {d U W : ℕ} {μ : ℕ → ℤ}
    {A B C : ℕ → ℤ} {keysB keysC : ℕ → ℕ}
    (R : Resources c lim d U W μ A B C keysB keysC) :
    Meets lim program 8 d c.args μ (time keysB keysC c.nA c.nB c.nC c.L)
      (fun ret ν => ret = (cleanupFlag A B C keysB keysC c.nA c.nB c.nC : ℤ) ∧
        Output ν keysB B c.nB c.outB c.valueB c.packedB c.lengthB ∧
        Output ν keysC C c.nC c.outC c.valueC c.packedC c.lengthC ∧ Kept μ ν c.outB ∧
          LightOriginalSurvivorStage.Above μ ν c.lengthC ∧ c.Unchanged keysB keysC μ ν) := by sorry
