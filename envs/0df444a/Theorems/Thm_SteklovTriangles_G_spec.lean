-- Prove2me | Theorems.Thm_SteklovTriangles_G_spec
-- name    : SteklovTriangles.G_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:00.435788+00:00
-- url     : https://prove2.me/theorems/aad8d90a-8b73-5fa6-88bb-290d07d26b4d
-- title:
--   Steklov Triangles: G spec
-- statement:
--   The Steklov Triangles construction uses the G spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/Reformulation.lean#L26-L37
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/Reformulation.lean#L26-L37

import Mathlib
import Definitions.Def_SteklovTriangles_Reformulation
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.G_spec (ρ a b : ℝ) (hd : 1 + ρ * b ≠ 0) :
    let d := 1 + ρ * b
    let G11 := 1 + ρ ^ 2 * a ^ 2 / d ^ 2
    let G12 := -(ρ * a) / d ^ 2
    let G22 := 1 / d ^ 2
    -- AᵀA = [[1, ρ a], [ρ a, ρ²a² + d²]]
    (1 * G11 + (ρ * a) * G12 = 1) ∧ (1 * G12 + (ρ * a) * G22 = 0) ∧
    ((ρ * a) * G11 + (ρ ^ 2 * a ^ 2 + d ^ 2) * G12 = 0) ∧
    ((ρ * a) * G12 + (ρ ^ 2 * a ^ 2 + d ^ 2) * G22 = 1) := by sorry
