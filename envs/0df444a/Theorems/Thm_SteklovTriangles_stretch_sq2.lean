-- Prove2me | Theorems.Thm_SteklovTriangles_stretch_sq2
-- name    : SteklovTriangles.stretch_sq2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:09.762145+00:00
-- url     : https://prove2.me/theorems/bd021e93-49b3-5358-b6c8-92cf5567df80
-- title:
--   Steklov Triangles: stretch sq2
-- statement:
--   Edge from the apex to `(0,0)`: `κ₂ = cos ψ + √3 sin ψ`.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/Reformulation.lean#L99-L103
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/Reformulation.lean#L99-L103

import Mathlib
import Definitions.Def_SteklovTriangles_Reformulation
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.stretch_sq2 (ρ c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((1 : ℝ) / 2 + ρ * c) ^ 2 + (Real.sqrt 3 / 2 + ρ * s) ^ 2
      = 1 + ρ * (c + Real.sqrt 3 * s) + ρ ^ 2 := by sorry
