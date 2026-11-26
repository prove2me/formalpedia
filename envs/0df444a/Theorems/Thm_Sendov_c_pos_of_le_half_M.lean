-- Prove2me | Theorems.Thm_Sendov_c_pos_of_le_half_M
-- name    : Sendov.c_pos_of_le_half_M
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:56:17.771797+00:00
-- url     : https://prove2.me/theorems/00dbb881-1b08-47ba-a925-3e011eaed7aa
-- title:
--   Sendov: c pos of le half M
-- statement:
--   Feasibility gives `α ≤ (n-1)/2`, and hence `c ≥ (1-B)/2 > 0`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L101-L111
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L101-L111

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.c_pos_of_le_half_M (hn : 2 ≤ n) (hα : 0 ≤ α) (hhalf : α ≤ M n / 2) : 0 < c n α := by sorry
