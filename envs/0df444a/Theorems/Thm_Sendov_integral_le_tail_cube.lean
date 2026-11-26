-- Prove2me | Theorems.Thm_Sendov_integral_le_tail_cube
-- name    : Sendov.integral_le_tail_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:06.070707+00:00
-- url     : https://prove2.me/theorems/b4ae274e-c3e7-5a2b-a8f7-3089eedbd6a2
-- title:
--   Sendov: integral le tail cube
-- statement:
--   The instance with weight `t³`, used by the large-degree argument.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L283-L289
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L283-L289

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_le_tail_cube {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * QQ c A t ^ r)
      ≤ 6 / (c ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4))) + QQ c A 1 ^ r / 4 := by sorry
