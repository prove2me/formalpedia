-- Prove2me | Theorems.Thm_ShiQMAConstructiveSchedule_copies_rounds_le
-- name    : ShiQMAConstructiveSchedule.copies_rounds_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T13:08:46.042312+00:00
-- url     : https://prove2.me/theorems/877fa307-e8f2-486e-8324-33af09f3d3fc
-- title:
--   Constructive QMA repetition uses polynomially many copies
-- statement:
--   Three to the constructive round count is bounded by an explicit constant depending on the target polynomial times a fixed power of n+1.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/24620b5/proofs/AMPUNI-constructive-schedule.lean#L59-L91

import Definitions.Def_ShiQMAConstructiveSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem ShiQMAConstructiveSchedule.copies_rounds_le (p : Polynomial ℕ) (n : ℕ) :
    3 ^ rounds p n ≤
      3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree) := by sorry
