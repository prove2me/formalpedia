-- Prove2me | Theorems.Thm_Sendov_integral_QQ_anti
-- name    : Sendov.integral_QQ_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:05.294048+00:00
-- url     : https://prove2.me/theorems/cced8d6a-c354-4d2e-a88d-252a95c60c6c
-- title:
--   Sendov: integral QQ anti
-- statement:
--   The integral is antitone in `c`: raising `c` lowers `QQ` pointwise on `[0,1]`.  Note that
--   nonnegativity is only needed for the *larger* `c`; for the smaller one it comes free from the
--   pointwise comparison.  (`Sendov.integral_anti` in `FiniteRange.Batch` is the same trick applied
--   to the degree instead.)
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L259-L270
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L259-L270

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_QQ_anti {c₁ c₂ A : ℝ} (hle : c₁ ≤ c₂) (hfeas : c₂ ^ 2 ≤ A) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c₂ A t ^ r)
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * QQ c₁ A t ^ r := by sorry
