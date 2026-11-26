-- Prove2me | Theorems.Thm_Sendov_U_eq
-- name    : Sendov.U_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:32.685799+00:00
-- url     : https://prove2.me/theorems/29658bf3-38ec-4cd9-973b-465f9decf73f
-- title:
--   Sendov: U eq
-- statement:
--   **`U` in closed form.**  The `n (n-2)` of the prefactor cancels against the same factor
--   in the sharp Beta constant, leaving a rational function plus a natural power of `√B`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L167-L179
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L167-L179

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.U_eq (hn : 5 ≤ n) (hα : 0 ≤ α) (hc : c n α ≠ 0) :
    U n α = 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + T1 n α + T2 n α := by sorry
