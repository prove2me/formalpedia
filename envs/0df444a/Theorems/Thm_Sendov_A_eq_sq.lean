-- Prove2me | Theorems.Thm_Sendov_A_eq_sq
-- name    : Sendov.A_eq_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:44:43.543058+00:00
-- url     : https://prove2.me/theorems/0fcefe8b-0127-4003-9b0f-9167ac65e544
-- title:
--   Sendov: A eq sq
-- statement:
--   With `α = (n-1)(1-a²)/2`, the `A` of `Sendov.Defs` is exactly `a²`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L58-L62
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L58-L62

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.A_eq_sq (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) : A n α = a ^ 2 := by sorry
