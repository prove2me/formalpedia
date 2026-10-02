-- Prove2me | Theorems.Thm_ShiQMACenteredGap_affine_schedule_le_rounds
-- name    : ShiQMACenteredGap.affine_schedule_le_rounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T01:05:55.081963+00:00
-- url     : https://prove2.me/theorems/403a21c8-561f-4ac8-9b83-0e5d2e3966a8
-- title:
--   Polynomial generator dominates an affine-logarithmic round budget
-- statement:
--   A monomial parameter makes the existing constructive round function at least any fixed affine-logarithmic budget.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L14-L24

import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.affine_schedule_le_rounds (A D n : Nat) :
    A + D * (Nat.log 2 (n + 1) + 1) ≤ rounds (schedulePolynomial A D) n := by sorry
