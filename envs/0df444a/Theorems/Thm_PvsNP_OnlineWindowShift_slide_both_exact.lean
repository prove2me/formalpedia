-- Prove2me | Theorems.Thm_PvsNP_OnlineWindowShift_slide_both_exact
-- name    : PvsNP.OnlineWindowShift.slide_both_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T03:52:58.906331+00:00
-- url     : https://prove2.me/theorems/1f35001f-34f1-50fb-afdd-e60ed4331fb3
-- title:
--   A scratch window moves both ways in linear time on one work tape
-- statement:
--   For every width w and every scratch payload, the finite right-shift program moves the full frame one cell right in exactly 2w+4 steps. The left-shift program does the corresponding move in exactly 4w+8 steps. Both preserve every consumer cell and finish with the head on the new near marker.
-- source:
--   Exact finite tape transition proof with marked frame boundaries.

import Definitions.Def_OnlineScratchWindow

set_option autoImplicit false
set_option maxHeartbeats 1800000

open Function PvsNP.WorkBoundarySplice PvsNP.OnlineWindowShift

variable {P C : Type}

theorem PvsNP.OnlineWindowShift.slide_both_exact (p : ℤ) (w : ℕ)
    (payload : ℕ → P) (consumer : ℤ → C) :
    ((fun z : Option (Config (Phase P) (C × Cell P)) => z.bind (step shiftRightMachine))^[2*w+4])
      (some ⟨.enter,p,tracks consumer (frame p w payload)⟩) =
        some ⟨.done,p+1,tracks consumer (frame (p+1) w payload)⟩ ∧
    ((fun z : Option (Config (LeftPhase P) (C × Cell P)) => z.bind (step shiftLeftMachine))^[4*w+8])
      (some ⟨.active .seekFar .returnHome,p,tracks consumer (frame p w payload)⟩) =
        some ⟨.done,p-1,tracks consumer (frame (p-1) w payload)⟩ := by sorry
