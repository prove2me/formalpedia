-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_meets
-- name    : ThreeSum.LightTernaryFixedChannelLoop.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:17.692224+00:00
-- url     : https://prove2.me/theorems/915f6ae7-88c0-46b1-9d85-b6429de5fc8e
-- title:
--   Light Ternary Fixed Channel Loop: meets
-- statement:
--   The Light Ternary Fixed Channel Loop construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L93-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L93-L101

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryFixedChannelLoop.meets {steps : List Channel} {entry cost : Channel→ℕ} {vals : List ℤ}
    {pMain : ℕ} (hmain : P[pMain]?=some (body steps entry vals.length))
    (μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop) (hd : d<lim.depth) (hI : I 0 μ)
    (hstep : ∀ i<steps.length, ∀ ν, I i ν →
      Meets lim P (entry (steps.getD i (0,0))) (d+1) vals ν
        (cost (steps.getD i (0,0))) (fun _ ξ => I (i+1) ξ)) :
    Meets lim P pMain d vals μ (time steps cost vals.length)
      (fun _ ν => I steps.length ν) := by sorry
