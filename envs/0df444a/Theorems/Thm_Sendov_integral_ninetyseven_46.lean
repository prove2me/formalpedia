-- Prove2me | Theorems.Thm_Sendov_integral_ninetyseven_46
-- name    : Sendov.integral_ninetyseven_46
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:19:05.804585+00:00
-- url     : https://prove2.me/theorems/db53cdc7-d0f3-51b2-9a02-4d8ab4c38a12
-- title:
--   Sendov: integral ninetyseven 46
-- statement:
--   The degree-97 moment at `k = 46`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L53-L57
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L53-L57

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov

theorem Sendov.integral_ninetyseven_46 (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 97 α t ^ 46)
      = pev Nmom97_46 α / ((L97_46 : ℝ) * (2 * M 97 * (3 + α)) ^ 46) := by sorry
