-- Prove2me | Theorems.Thm_Sendov_T1_le
-- name    : Sendov.T1_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:36.562097+00:00
-- url     : https://prove2.me/theorems/078b8841-039d-498f-b679-6f860bd37211
-- title:
--   Sendov: T1 le
-- statement:
--   `T1` is bounded by its value at `n = 101`, up to `1%`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L184-L231
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L184-L231

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.T1_le (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    T1 n α ≤ 101 / 100 * T1 101 α := by sorry
