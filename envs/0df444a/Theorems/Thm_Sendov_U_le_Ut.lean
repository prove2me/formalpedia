-- Prove2me | Theorems.Thm_Sendov_U_le_Ut
-- name    : Sendov.U_le_Ut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:48:26.245115+00:00
-- url     : https://prove2.me/theorems/2bbea79b-a446-46b8-8470-df8988644e98
-- title:
--   Sendov: U le Ut
-- statement:
--   **`U` is bounded by an expression in `α` alone**, for every `n ≥ 101`.  This is where the
--   degree leaves the argument.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L317-L359
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L317-L359

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.U_le_Ut (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : U n α ≤ Ut α := by sorry
