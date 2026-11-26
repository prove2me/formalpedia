-- Prove2me | Theorems.Thm_Sendov_rpow_B_eq
-- name    : Sendov.rpow_B_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:20.684793+00:00
-- url     : https://prove2.me/theorems/eb06a95b-794f-4992-b323-b51506054d8a
-- title:
--   Sendov: rpow B eq
-- statement:
--   The real power of `B` in `Sendov.U` is a natural power of `√B`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L146-L155
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L146-L155

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.rpow_B_eq (hn : 4 ≤ n) (hα : 0 ≤ α) :
    (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) = Real.sqrt (α / (3 + α)) ^ (n - 4) := by sorry
