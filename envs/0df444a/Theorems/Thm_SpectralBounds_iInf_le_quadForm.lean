-- Prove2me | Theorems.Thm_SpectralBounds_iInf_le_quadForm
-- name    : SpectralBounds.iInf_le_quadForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:18:53.86734+00:00
-- url     : https://prove2.me/theorems/68c5f3bc-47d8-519c-9e00-9082b385c2ba
-- title:
--   Spectral Bounds: i Inf le quad Form
-- statement:
--   Rayleigh lower bound: `λ_min ‖x‖² ≤ xᵀ M x`.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L67-L72
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L67-L72

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

theorem SpectralBounds.iInf_le_quadForm (hM : M.IsHermitian) (x : W → ℝ) :
    (⨅ i, hM.eigenvalues i) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by sorry
