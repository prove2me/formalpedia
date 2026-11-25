-- Prove2me | Theorems.Thm_SteklovTriangles_stretch_sq1
-- name    : SteklovTriangles.stretch_sq1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:28.502575+00:00
-- url     : https://prove2.me/theorems/4165a19b-d264-45e4-887e-6808a8f7ef30
-- title:
--   Steklov Triangles: stretch sq1
-- statement:
--   Edge from `(1,0)` to the apex `(1/2 + ρ cos ψ, √3/2 + ρ sin ψ)`: `κ₁ = -cos ψ + √3 sin ψ`.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/Reformulation.lean#L92-L96
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/Reformulation.lean#L92-L96

import Mathlib
import Definitions.Def_SteklovTriangles_Reformulation
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.stretch_sq1 (ρ c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (-(1 : ℝ) / 2 + ρ * c) ^ 2 + (Real.sqrt 3 / 2 + ρ * s) ^ 2
      = 1 + ρ * (-c + Real.sqrt 3 * s) + ρ ^ 2 := by sorry
