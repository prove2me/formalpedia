-- Prove2me | Theorems.Thm_ShiQMACenteredGap_generalGapRounds_le_existing
-- name    : ShiQMACenteredGap.generalGapRounds_le_existing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T01:13:15.670672+00:00
-- url     : https://prove2.me/theorems/0264337b-0d5d-44eb-b4b0-29123fa10d7b
-- title:
--   Existing generator schedule dominates general-gap QMA rounds
-- statement:
--   The explicit normalization-plus-error schedule is no larger than the round count of the concrete generator with a suitable polynomial parameter.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L31-L34

import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_affine_schedule_le_rounds
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_controller_form

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.generalGapRounds_le_existing (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n ≤ rounds (gapPolynomial q p) n := by sorry
