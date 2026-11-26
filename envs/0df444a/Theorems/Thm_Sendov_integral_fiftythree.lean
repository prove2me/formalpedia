-- Prove2me | Theorems.Thm_Sendov_integral_fiftythree
-- name    : Sendov.integral_fiftythree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:19:00.173143+00:00
-- url     : https://prove2.me/theorems/a1825f17-7b20-40a6-af43-43a544235275
-- title:
--   Sendov: integral fiftythree
-- statement:
--   The degree-53 moment.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree53Packed.lean#L57-L61
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree53Packed.lean#L57-L61

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree53Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 1000000
open Sendov

theorem Sendov.integral_fiftythree (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 53 α t ^ 24)
      = pev Nmom53 α / ((L53 : ℝ) * (2 * M 53 * (3 + α)) ^ 24) := by sorry
