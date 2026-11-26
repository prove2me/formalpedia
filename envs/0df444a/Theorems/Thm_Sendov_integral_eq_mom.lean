-- Prove2me | Theorems.Thm_Sendov_integral_eq_mom
-- name    : Sendov.integral_eq_mom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:07.239871+00:00
-- url     : https://prove2.me/theorems/28280a62-468f-5048-8cd5-88f873f26e91
-- title:
--   Sendov: integral eq mom
-- statement:
--   **Even degrees.**  The integral in `Sendov.R` is exactly a moment.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L38-L42
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L38-L42

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}

theorem Sendov.integral_eq_mom (k : ℕ) (hk : ((n : ℝ) - 4) / 2 = (k : ℕ)) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) = mom n α k := by sorry
