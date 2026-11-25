-- Prove2me | Theorems.Thm_SpectralBounds_quadForm_le_iSup
-- name    : SpectralBounds.quadForm_le_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:18:59.490616+00:00
-- url     : https://prove2.me/theorems/e5604884-022a-5bd6-ae1e-bc4bab081fe4
-- title:
--   Spectral Bounds: quad Form le i Sup
-- statement:
--   Rayleigh upper bound: `xᵀ M x ≤ λ_max ‖x‖²`.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L59-L64
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L59-L64

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

theorem SpectralBounds.quadForm_le_iSup (hM : M.IsHermitian) (x : W → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ (⨆ i, hM.eigenvalues i) * (x ⬝ᵥ x) := by sorry
