-- Prove2me | Theorems.Thm_SteklovTriangles_area_corollary
-- name    : SteklovTriangles.area_corollary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:41.695939+00:00
-- url     : https://prove2.me/theorems/5472a871-fa44-562b-a111-45bba17b3a5d
-- title:
--   Steklov Triangles: area corollary
-- statement:
--   The fixed-area corollary as real algebra: from `σ L ≤ S` and `A ≤ k L^2`
--   we get `σ √A ≤ S √k`.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L83-L91
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L83-L91

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.area_corollary (σ L A S k : ℝ) (hσ : 0 ≤ σ) (hL : 0 < L) (hk : 0 ≤ k)
    (hper : σ * L ≤ S) (hiso : A ≤ k * L ^ 2) : σ * Real.sqrt A ≤ S * Real.sqrt k := by sorry
