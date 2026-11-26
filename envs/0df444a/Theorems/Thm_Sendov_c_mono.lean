-- Prove2me | Theorems.Thm_Sendov_c_mono
-- name    : Sendov.c_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:30.535805+00:00
-- url     : https://prove2.me/theorems/6b2d45f1-55e6-40c9-bff5-d17e3de32538
-- title:
--   Sendov: c mono
-- statement:
--   `c` increases with `n`: raising the degree moves `c` towards `1 - B/2`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L135-L143
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L135-L143

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.c_mono {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : c m α ≤ c n α := by sorry
