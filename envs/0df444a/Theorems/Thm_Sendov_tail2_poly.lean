-- Prove2me | Theorems.Thm_Sendov_tail2_poly
-- name    : Sendov.tail2_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:14.811826+00:00
-- url     : https://prove2.me/theorems/03db6c3e-1126-4d68-9d54-9c996b462198
-- title:
--   Sendov: tail2 poly
-- statement:
--   The geometric step for the second tail term: on `0 ≤ α ≤ 17` and `n = 101 + k ≥ 101`,
--
--     `12 A_{n+1}² (n+1) n (n-1) ≤ 13 A_n² n (n-1)(n-2)`,
--
--   after clearing the denominators `n²` and `(n-1)²` of `A_{n+1}` and `A_n`.  Together with
--   `√B ≤ 12/13` this makes the step ratio less than one.  A Bernstein certificate in `α` on
--   `[0,17]` with all coefficients positive combinations of powers of `k`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L105-L130
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L105-L130

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.tail2_poly {k α : ℝ} (hk : 0 ≤ k) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2
      ≤ 13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2 := by sorry
