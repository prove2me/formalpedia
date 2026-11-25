-- Prove2me | Theorems.Thm_SteklovTriangles_triangle_isoperimetric_heron
-- name    : SteklovTriangles.triangle_isoperimetric_heron
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:44.068323+00:00
-- url     : https://prove2.me/theorems/029e8a6e-3cf1-545f-88f3-36adc6a906f3
-- title:
--   Steklov Triangles: triangle isoperimetric heron
-- statement:
--   The isoperimetric inequality for triangles in Heron form.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L27-L38
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L27-L38

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.triangle_isoperimetric_heron (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b) :
    27 * ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)) ≤ (a + b + c) ^ 4 := by sorry
