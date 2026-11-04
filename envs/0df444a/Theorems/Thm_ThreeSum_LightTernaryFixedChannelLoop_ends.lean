-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_ends
-- name    : ThreeSum.LightTernaryFixedChannelLoop.ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:21.178612+00:00
-- url     : https://prove2.me/theorems/c18bdf73-f8e3-47f9-ae51-3d7fac538254
-- title:
--   Light Ternary Fixed Channel Loop: ends
-- statement:
--   The finite traversal executes each registered concrete channel procedure.
--   Its only callee premise is the ordinary `Meets` execution theorem at that
--   procedure's program index; the theorem introduces no abstract operation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L55-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L55-L91

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryFixedChannelLoop.ends (steps : List Channel) (entry : Channel→ℕ) (cost : Channel→ℕ)
    (vals : List ℤ) (loc μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop)
    (hd : d<lim.depth) (hloc : ∀ i<vals.length, loc i=frame vals i)
    (hI : I 0 μ)
    (hstep : ∀ i<steps.length, ∀ ν, I i ν →
      Meets lim P (entry (steps.getD i (0,0))) (d+1) vals ν
        (cost (steps.getD i (0,0))) (fun _ ξ => I (i+1) ξ)) :
    Ends lim P d (body steps entry vals.length) ⟨loc,μ⟩
      (time steps cost vals.length) (fun σ => I steps.length σ.mem) := by sorry
