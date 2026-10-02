-- Prove2me | Theorems.Thm_ShiQMAConstructiveSchedule_error_rounds
-- name    : ShiQMAConstructiveSchedule.error_rounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T13:04:50.88867+00:00
-- url     : https://prove2.me/theorems/42627765-22e3-47c3-88a6-da763c46126a
-- title:
--   Logarithmic QMA repetition rounds reach exponential target error
-- statement:
--   The scalar majority error after the constructive round count is at most 2 raised to minus the target polynomial value.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/24620b5/proofs/AMPUNI-constructive-schedule.lean#L48-L56

import Definitions.Def_ShiQMAConstructiveSchedule
import Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem ShiQMAConstructiveSchedule.error_rounds (p : Polynomial ℕ) (n : ℕ) :
    error (rounds p n) ≤ ((1 : ℝ) / 2) ^ (p.eval n) := by sorry
