-- Prove2me | Theorems.Thm_SteklovTriangles_amgm3_eq
-- name    : SteklovTriangles.amgm3_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:35.87694+00:00
-- url     : https://prove2.me/theorems/52313086-1528-592d-8114-0aefc194572f
-- title:
--   Steklov Triangles: amgm3 eq
-- statement:
--   Equality in AM–GM (three variables) forces equal arguments.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L41-L61
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L41-L61

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.amgm3_eq (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : 27 * (x * y * z) = (x + y + z) ^ 3) : x = y ∧ y = z := by sorry
