-- Prove2me | Theorems.Thm_Sendov_mom_one
-- name    : Sendov.mom_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:30.763219+00:00
-- url     : https://prove2.me/theorems/48211196-1a4c-536a-bb80-c5aaf3992b59
-- title:
--   Sendov: mom one
-- statement:
--   `∫ t in 0..1, t ^ 3 * Q`
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L77-L79
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L77-L79

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}

theorem Sendov.mom_one (n : ℕ) (α : ℝ) : mom n α 1 = 1 / 4 - 2 * c n α / 5 + A n α / 6 := by sorry
