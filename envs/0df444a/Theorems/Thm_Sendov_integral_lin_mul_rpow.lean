-- Prove2me | Theorems.Thm_Sendov_integral_lin_mul_rpow
-- name    : Sendov.integral_lin_mul_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:37.077799+00:00
-- url     : https://prove2.me/theorems/2d95f9ab-44ea-4d72-9528-0608b1494bbb
-- title:
--   Sendov: integral lin mul rpow
-- statement:
--   The Beta integral `B(2, s+1)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L42-L69
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L42-L69

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_lin_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s) = 1 / ((s + 1) * (s + 2)) := by sorry
