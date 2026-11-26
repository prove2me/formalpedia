-- Prove2me | Theorems.Thm_Sendov_integral_chord_lin
-- name    : Sendov.integral_chord_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:42.759517+00:00
-- url     : https://prove2.me/theorems/dd28fcd8-1c7c-4d64-8368-6a012f52e275
-- title:
--   Sendov: integral chord lin
-- statement:
--   The chord integral with weight `t`, over `[0, 1/c]`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L123-L141
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L123-L141

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_chord_lin {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t * (1 - c * t) ^ s) = 1 / (c ^ 2 * ((s + 1) * (s + 2))) := by sorry
