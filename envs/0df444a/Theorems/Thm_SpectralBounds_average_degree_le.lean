-- Prove2me | Theorems.Thm_SpectralBounds_average_degree_le
-- name    : SpectralBounds.average_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:20.552975+00:00
-- url     : https://prove2.me/theorems/48b97974-06ac-5119-8710-5a1e1d34c0c0
-- title:
--   Spectral Bounds: average degree le
-- statement:
--   The average degree `2 |E| / n` is at most the largest adjacency eigenvalue.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L182-L194
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L182-L194

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

theorem SpectralBounds.average_degree_le :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i := by sorry
