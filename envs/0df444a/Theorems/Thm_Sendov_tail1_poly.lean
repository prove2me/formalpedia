-- Prove2me | Theorems.Thm_Sendov_tail1_poly
-- name    : Sendov.tail1_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:29.865653+00:00
-- url     : https://prove2.me/theorems/979b4f7b-4c13-4128-949f-dc2615bb34f5
-- title:
--   Sendov: tail1 poly
-- statement:
--   The allowance for the first tail term: on `0 ≤ α ≤ 17` and `N = 100 + j ≥ 100`,
--
--     `(N-2α)² / (N (N+3)(N+5)) ≤ (101/100) (100-2α)² / (100 · 103 · 105)`.
--
--   A Bernstein certificate in `α` on `[0,17]`, whose coefficients are polynomials in `j`.  The
--   top one, `439956 j³ + 27356448 j² - 366591060 j + 4711014000`, has a negative linear
--   coefficient; it is nonnegative because its quadratic part has negative discriminant.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L75-L96
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L75-L96

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.tail1_poly {j α : ℝ} (hj : 0 ≤ j) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    108150000 * (100 + j - 2 * α) ^ 2
      ≤ 101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j)) := by sorry
