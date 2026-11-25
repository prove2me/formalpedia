-- Prove2me | Theorems.Thm_SpectralBounds_iInf_eigenvalues_le_neg_one
-- name    : SpectralBounds.iInf_eigenvalues_le_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:23:42.861093+00:00
-- url     : https://prove2.me/theorems/58bb424f-5efa-4957-9fe3-b7c677191ca8
-- title:
--   Spectral Bounds: i Inf eigenvalues le neg one
-- statement:
--   The Spectral Bounds construction uses the i Inf eigenvalues le neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L130-L139
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L130-L139

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
omit [Nonempty V]

theorem SpectralBounds.iInf_eigenvalues_le_neg_one (hE : G.edgeSet.Nonempty) :
    (⨅ i, hA.eigenvalues i) ≤ -1 := by sorry
