-- Prove2me | Theorems.Thm_Sendov_integral_ninetyseven_47
-- name    : Sendov.integral_ninetyseven_47
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:19:19.111607+00:00
-- url     : https://prove2.me/theorems/6358eaad-7f13-5f41-808c-a8765cfc0004
-- title:
--   Sendov: integral ninetyseven 47
-- statement:
--   The degree-97 moment at `k = 47`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L89-L93
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L89-L93

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov

theorem Sendov.integral_ninetyseven_47 (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 97 α t ^ 47)
      = pev Nmom97_47 α / ((L97_47 : ℝ) * (2 * M 97 * (3 + α)) ^ 47) := by sorry
