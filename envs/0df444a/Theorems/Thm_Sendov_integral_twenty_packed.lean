-- Prove2me | Theorems.Thm_Sendov_integral_twenty_packed
-- name    : Sendov.integral_twenty_packed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:29.733806+00:00
-- url     : https://prove2.me/theorems/3f740679-c5b5-5bc0-8664-f44663ed3bfe
-- title:
--   Sendov: integral twenty packed
-- statement:
--   The degree-twenty moment, via the packed route.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20Packed.lean#L51-L55
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20Packed.lean#L51-L55

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000
open Sendov

theorem Sendov.integral_twenty_packed (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmom20 α / ((L20 : ℝ) * (2 * M 20 * (3 + α)) ^ 8) := by sorry
