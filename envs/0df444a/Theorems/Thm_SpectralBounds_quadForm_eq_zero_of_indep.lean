-- Prove2me | Theorems.Thm_SpectralBounds_quadForm_eq_zero_of_indep
-- name    : SpectralBounds.quadForm_eq_zero_of_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:08.842161+00:00
-- url     : https://prove2.me/theorems/e5068313-2a87-59ce-8eed-b77a5257d5b2
-- title:
--   Spectral Bounds: quad Form eq zero of indep
-- statement:
--   The quadratic form of the adjacency matrix vanishes on vectors supported on an
--   independent set.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L92-L100
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L92-L100

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
omit [DecidableEq V] [Nonempty V]

theorem SpectralBounds.quadForm_eq_zero_of_indep (z : V → ℝ) (hz : ∀ u v, G.Adj u v → z u = 0 ∨ z v = 0) :
    z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0 := by sorry
