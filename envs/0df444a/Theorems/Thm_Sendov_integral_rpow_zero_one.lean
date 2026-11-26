-- Prove2me | Theorems.Thm_Sendov_integral_rpow_zero_one
-- name    : Sendov.integral_rpow_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:58.0999+00:00
-- url     : https://prove2.me/theorems/e55a31a1-4c1c-5667-ab6b-bb04057a5f12
-- title:
--   Sendov: integral rpow zero one
-- statement:
--   `∫₀¹ xˢ dx = 1/(s+1)` for `s > -1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L32-L35
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L32-L35

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_rpow_zero_one {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by sorry
