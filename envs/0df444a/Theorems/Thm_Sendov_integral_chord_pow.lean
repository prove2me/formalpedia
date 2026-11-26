-- Prove2me | Theorems.Thm_Sendov_integral_chord_pow
-- name    : Sendov.integral_chord_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:37.133843+00:00
-- url     : https://prove2.me/theorems/568a87ab-3fe7-5699-b0fe-da59508063e8
-- title:
--   Sendov: integral chord pow
-- statement:
--   The chord integral with weight `t³`, over `[0, 1/c]`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L144-L163
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L144-L163

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_chord_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 3 * (1 - c * t) ^ s)
      = 6 / (c ^ 4 * ((s + 1) * (s + 2) * (s + 3) * (s + 4))) := by sorry
