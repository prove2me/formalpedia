-- Prove2me | Theorems.Thm_SpectralBounds_exists_unit_eigenvector_iSup
-- name    : SpectralBounds.exists_unit_eigenvector_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:20.878241+00:00
-- url     : https://prove2.me/theorems/a944f198-e28f-4740-a936-a50bb5a23058
-- title:
--   Spectral Bounds: exists unit eigenvector i Sup
-- statement:
--   There is a unit eigenvector for the largest eigenvalue.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L75-L83
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L75-L83

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

theorem SpectralBounds.exists_unit_eigenvector_iSup [Nonempty W] (hM : M.IsHermitian) :
    ∃ x : W → ℝ, M *ᵥ x = (⨆ i, hM.eigenvalues i) • x ∧ x ⬝ᵥ x = 1 := by sorry
