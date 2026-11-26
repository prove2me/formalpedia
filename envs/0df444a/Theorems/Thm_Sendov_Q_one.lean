-- Prove2me | Theorems.Thm_Sendov_Q_one
-- name    : Sendov.Q_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:43.188596+00:00
-- url     : https://prove2.me/theorems/94aee982-acaa-4bba-93ab-8cf0fe4a798c
-- title:
--   Sendov: Q one
-- statement:
--   `Q n α 1 = B = α / (3 + α)`: the substituted quadratic takes at `t = 1` the value that
--   the simplified polar inequality `β(1) < α / (3 + α)` prescribes.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L72-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L72-L77

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.Q_one (hn : 2 ≤ n) (hα : 0 ≤ α) : Q n α 1 = α / (3 + α) := by sorry
