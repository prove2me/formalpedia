-- Prove2me | Theorems.Thm_SteklovTriangles_triangle_isoperimetric_heron_eq
-- name    : SteklovTriangles.triangle_isoperimetric_heron_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:51:00.722342+00:00
-- url     : https://prove2.me/theorems/8527e2b0-3793-4e17-b51b-831384310844
-- title:
--   Steklov Triangles: triangle isoperimetric heron eq
-- statement:
--   Equality in the Heron-form isoperimetric inequality only for the equilateral triangle.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L64-L79
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L64-L79

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.triangle_isoperimetric_heron_eq (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b)
    (heq : 27 * ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)) = (a + b + c) ^ 4) :
    a = b ∧ b = c := by sorry
