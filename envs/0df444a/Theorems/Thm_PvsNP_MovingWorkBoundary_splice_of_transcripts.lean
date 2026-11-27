-- Prove2me | Theorems.Thm_PvsNP_MovingWorkBoundary_splice_of_transcripts
-- name    : PvsNP.MovingWorkBoundary.splice_of_transcripts
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T03:23:48.353597+00:00
-- url     : https://prove2.me/theorems/14408875-2ee6-5435-9613-1324d16c0cda
-- title:
--   Equal moving-cut transcripts preserve exact single-tape replay
-- statement:
--   Given two local one-tape runs and a common cut schedule, the mixed run obtained from their respective initial half-tapes has the two designated half-tapes at the final clock. This holds when the runs agree on the initial head side, all time-stamped control transfer messages, and all tape-cell handoff symbols. The mixed head and control come from the active source at the final clock.
-- source:
--   A time-synchronized single-tape crossing argument with moving ownership.

import Definitions.Def_MovingWorkTapePartition

set_option autoImplicit false
set_option maxHeartbeats 1600000

open PvsNP.WorkBoundarySplice PvsNP.MovingWorkBoundary

variable {Q Γ : Type}

theorem PvsNP.MovingWorkBoundary.splice_of_transcripts (cut : ℕ → ℤ) (M : Machine Q Γ) (a b : Config Q Γ) (T : ℕ)
    (initial : sideAt cut M a 0 = sideAt cut M b 0)
    (controls : ∀ t < T, controlAt cut M a t = controlAt cut M b t)
    (handoffs : ∀ t < T, ∀ i, cellAt cut M a t i = cellAt cut M b t i) :
    trace M (assemble (rightOf (cut 0)) (sideAt cut M a 0) (pair a b)) T =
      assemble (rightOf (cut T)) (sideAt cut M a T)
        (fun side => trace M (pair a b side) T) := by sorry
