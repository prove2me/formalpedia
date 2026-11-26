-- Prove2me | Theorems.Thm_Sendov_integral_le_mom
-- name    : Sendov.integral_le_mom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:12:32.087128+00:00
-- url     : https://prove2.me/theorems/33d0951a-1509-4077-8552-c3826995938d
-- title:
--   Sendov: integral le mom
-- statement:
--   **Odd degrees.**  After `Sendov.integral_rpow_le` has removed the square root, the
--   integral in `Sendov.R` is bounded by a combination of two moments.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L46-L65
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L46-L65

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}

theorem Sendov.integral_le_mom (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ mom n α (k + 1) / (2 * w) + w / 2 * mom n α k := by sorry
