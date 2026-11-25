-- Prove2me | Theorems.Thm_SpectralBounds_dotProduct_adjMatrix_mulVec_comm
-- name    : SpectralBounds.dotProduct_adjMatrix_mulVec_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:23:17.994409+00:00
-- url     : https://prove2.me/theorems/c6d2e031-06b8-51f8-8633-90c66c346ff9
-- title:
--   Spectral Bounds: dot Product adj Matrix mul Vec comm
-- statement:
--   The Spectral Bounds construction uses the dot Product adj Matrix mul Vec comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L103-L105
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L103-L105

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

theorem SpectralBounds.dotProduct_adjMatrix_mulVec_comm (x z : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = z ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by sorry
