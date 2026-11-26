-- Prove2me | Theorems.Thm_Sendov_T2_le
-- name    : Sendov.T2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:30.688298+00:00
-- url     : https://prove2.me/theorems/3b23199b-faca-5170-a663-e051c40b89d2
-- title:
--   Sendov: T2 le
-- statement:
--   `T2` is bounded by its value at `n = 101`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L303-L306
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L303-L306

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.T2_le (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 n α ≤ T2 101 α := by sorry
