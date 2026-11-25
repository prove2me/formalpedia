-- Prove2me | Theorems.Thm_SteklovTriangles_amgm3
-- name    : SteklovTriangles.amgm3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:47.916094+00:00
-- url     : https://prove2.me/theorems/fc53db0a-2bff-4750-a5b3-312d8f58da58
-- title:
--   Steklov Triangles: amgm3
-- statement:
--   AM–GM for three nonnegative reals, in polynomial form.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L18-L24
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L18-L24

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.amgm3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 := by sorry
