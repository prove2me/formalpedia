-- Prove2me | Theorems.Thm_Sendov_c_ge_of_large
-- name    : Sendov.c_ge_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:47.585636+00:00
-- url     : https://prove2.me/theorems/f493afa7-def2-508c-8563-7dc610aa7238
-- title:
--   Sendov: c ge of large
-- statement:
--   On the large-degree range `c` is bounded below, hence positive.  For `n ≥ 101` and
--   `α ≤ 17` this gives `c ≥ 81/200`, which is `(3)` of the write-up.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L71-L84
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L71-L84

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}

theorem Sendov.c_ge_of_large (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : 81 / 200 ≤ c n α := by sorry
