-- Prove2me | Theorems.Thm_Sendov_Q_succ_sub
-- name    : Sendov.Q_succ_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:50.502792+00:00
-- url     : https://prove2.me/theorems/88073fa5-6366-42a5-be6a-d6bb29e6c04a
-- title:
--   Sendov: Q succ sub
-- statement:
--   **The degree step.**  Raising `n` by one lowers `Q` by a multiple of `t(1-t)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L58-L69
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L58-L69

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
set_option autoImplicit false
open Sendov
variable {α t : ℝ}

theorem Sendov.Q_succ_sub (n : ℕ) (hn : 2 ≤ n) (hα : 0 ≤ α) (t : ℝ) :
    Q (n + 1) α t = Q n α t - (2 * α / ((n : ℝ) * ((n : ℝ) - 1))) * t * (1 - t) := by sorry
