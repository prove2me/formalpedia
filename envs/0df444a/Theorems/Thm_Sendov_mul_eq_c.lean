-- Prove2me | Theorems.Thm_Sendov_mul_eq_c
-- name    : Sendov.mul_eq_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:45:20.263807+00:00
-- url     : https://prove2.me/theorems/b2c5fe71-589a-4bfe-9147-c312d896b684
-- title:
--   Sendov: mul eq c
-- statement:
--   `ax = 1 - β(1)/2 - α/(n-1)`: the blog post's rearrangement of `β(1) = 1 - 2ax + a²`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L40-L45
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L40-L45

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}

theorem Sendov.mul_eq_c (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    a * x = 1 - QQ (a * x) (a ^ 2) 1 / 2 - α / M n := by sorry
