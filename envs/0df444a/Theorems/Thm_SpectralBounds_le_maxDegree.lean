-- Prove2me | Theorems.Thm_SpectralBounds_le_maxDegree
-- name    : SpectralBounds.le_maxDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:27.330566+00:00
-- url     : https://prove2.me/theorems/bdb31083-52a3-443b-a998-28cf457f2edd
-- title:
--   Spectral Bounds: le max Degree
-- statement:
--   The largest adjacency eigenvalue is at most the maximum degree.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L197-L218
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L197-L218

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix

theorem SpectralBounds.le_maxDegree : ⨆ i, hA.eigenvalues i ≤ G.maxDegree := by sorry
