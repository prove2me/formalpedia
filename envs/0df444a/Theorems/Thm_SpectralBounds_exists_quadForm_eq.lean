-- Prove2me | Theorems.Thm_SpectralBounds_exists_quadForm_eq
-- name    : SpectralBounds.exists_quadForm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:05.426485+00:00
-- url     : https://prove2.me/theorems/8efd27e0-809b-54f7-ab58-ad21ea7b750f
-- title:
--   Spectral Bounds: exists quad Form eq
-- statement:
--   Expansion of the quadratic form of a real symmetric matrix in an orthonormal eigenbasis.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L42-L56
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L42-L56

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
variable {W : Type*} [Fintype W] [DecidableEq W] {M : Matrix W W ℝ}
open Matrix

theorem SpectralBounds.exists_quadForm_eq (hM : M.IsHermitian) (x : W → ℝ) :
    ∃ y : W → ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ i, hM.eigenvalues i * y i ^ 2 ∧
      x ⬝ᵥ x = ∑ i, y i ^ 2 := by sorry
