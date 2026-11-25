-- Prove2me | Theorems.Thm_SteklovTriangles_int_x_sin_sq
-- name    : SteklovTriangles.int_x_sin_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:55.462946+00:00
-- url     : https://prove2.me/theorems/f51c3101-b8a2-5faf-9213-755d40277c32
-- title:
--   Steklov Triangles: int x sin sq
-- statement:
--   The Steklov Triangles construction uses the int x sin sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/CosBound.lean#L18-L49
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/CosBound.lean#L18-L49

import Mathlib
import Definitions.Def_SteklovTriangles_CosBound
set_option autoImplicit false
open SteklovTriangles
open Real intervalIntegral

theorem SteklovTriangles.int_x_sin_sq (p : ℝ) :
    ∫ x in (0:ℝ)..p, x * sin (π * x) ^ 2
      = p ^ 2 / 4 - p * sin (2 * π * p) / (4 * π) - (cos (2 * π * p) - 1) / (8 * π ^ 2) := by sorry
