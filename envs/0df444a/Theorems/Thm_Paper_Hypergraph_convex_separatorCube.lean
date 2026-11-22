-- Prove2me | Theorems.Thm_Paper_Hypergraph_convex_separatorCube
-- name    : Paper.Hypergraph.convex_separatorCube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:34.851826+00:00
-- url     : https://prove2.me/theorems/21d2065a-3ab6-4dde-850b-c97b46e87794
-- title:
--   Hypergraph: convex separator Cube
-- statement:
--   The Hypergraph construction uses the convex separator Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2213-L2231
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2213-L2231

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.convex_separatorCube (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (θ : ℝ) : Convex ℝ (H.separatorCube γ θ) := by sorry
