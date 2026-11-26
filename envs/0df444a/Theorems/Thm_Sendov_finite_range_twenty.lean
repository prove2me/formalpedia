-- Prove2me | Theorems.Thm_Sendov_finite_range_twenty
-- name    : Sendov.finite_range_twenty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:19:05.886676+00:00
-- url     : https://prove2.me/theorems/674c9799-fb20-4c4e-9ae1-4535a0991440
-- title:
--   Sendov: finite range twenty
-- statement:
--   **The finite-range claim in degree twenty.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L127-L159
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L127-L159

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.finite_range_twenty (hα : 0 ≤ α) (hfeas : c 20 α ^ 2 ≤ A 20 α) : R 20 α < 1 := by sorry
