-- Prove2me | Theorems.Thm_Sendov_integral_le_tail_lin
-- name    : Sendov.integral_le_tail_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:00.109661+00:00
-- url     : https://prove2.me/theorems/05781e0b-124a-552e-ad58-6ad77133dfde
-- title:
--   Sendov: integral le tail lin
-- statement:
--   The instance with weight `t`, used for `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L273-L280
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L273-L280

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_le_tail_lin {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t * QQ c A t ^ r)
      ≤ 1 / (c ^ 2 * ((r + 1) * (r + 2))) + QQ c A 1 ^ r / 2 := by sorry
