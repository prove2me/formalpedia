-- Prove2me | Theorems.Thm_SteklovTriangles_area_corollary_strict
-- name    : SteklovTriangles.area_corollary_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:50:51.698898+00:00
-- url     : https://prove2.me/theorems/ba548563-fc8a-4fc3-996c-28e3fa9634e9
-- title:
--   Steklov Triangles: area corollary strict
-- statement:
--   Strict version: strictness of the perimeter inequality gives a strict area inequality.
--
--   Source: https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L94-L103
-- source:
--   https://github.com/jasondavies/steklov-triangles/blob/9bdb5c5f9e03c02b363058e72eb95d19b5853e36/SteklovTriangles/AreaCorollary.lean#L94-L103

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
set_option autoImplicit false
open SteklovTriangles

theorem SteklovTriangles.area_corollary_strict (σ L A S k : ℝ) (hσ : 0 ≤ σ) (hL : 0 < L) (hk : 0 < k)
    (hper : σ * L < S) (hiso : A ≤ k * L ^ 2) : σ * Real.sqrt A < S * Real.sqrt k := by sorry
