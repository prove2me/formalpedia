-- Prove2me | Theorems.Thm_Sendov_finite_range_six
-- name    : Sendov.finite_range_six
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:16:47.118888+00:00
-- url     : https://prove2.me/theorems/4de677ba-d1c5-47b3-8631-99d549c81a05
-- title:
--   Sendov: finite range six
-- statement:
--   **The finite-range claim in degree six.**  Note that no upper bound on `α` is assumed:
--   the feasibility constraint supplies one.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L73-L84
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L73-L84

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.finite_range_six (hα : 0 ≤ α) (hfeas : c 6 α ^ 2 ≤ A 6 α) : R 6 α < 1 := by sorry
