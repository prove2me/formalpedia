-- Prove2me | Theorems.Thm_Sendov_mom_two
-- name    : Sendov.mom_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:17.179741+00:00
-- url     : https://prove2.me/theorems/50aaf162-1810-473a-94f1-0a7260ccf76d
-- title:
--   Sendov: mom two
-- statement:
--   `∫ t in 0..1, t ^ 3 * Q ^ 2`
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L82-L86
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L82-L86

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}

theorem Sendov.mom_two (n : ℕ) (α : ℝ) :
    mom n α 2 = 1 / 4 - 4 * c n α / 5 + (2 * c n α ^ 2 / 3 + A n α / 3)
      - 4 * c n α * A n α / 7 + A n α ^ 2 / 8 := by sorry
