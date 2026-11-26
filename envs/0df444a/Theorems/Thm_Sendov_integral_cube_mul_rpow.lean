-- Prove2me | Theorems.Thm_Sendov_integral_cube_mul_rpow
-- name    : Sendov.integral_cube_mul_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:31.983803+00:00
-- url     : https://prove2.me/theorems/50ac7437-35da-4828-b99b-d202ae76654e
-- title:
--   Sendov: integral cube mul rpow
-- statement:
--   The Beta integral `B(4, s+1)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L72-L113
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L72-L113

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_cube_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = 6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) := by sorry
