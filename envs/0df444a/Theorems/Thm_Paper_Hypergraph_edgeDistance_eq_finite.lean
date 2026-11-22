-- Prove2me | Theorems.Thm_Paper_Hypergraph_edgeDistance_eq_finite
-- name    : Paper.Hypergraph.edgeDistance_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:02.954343+00:00
-- url     : https://prove2.me/theorems/5ce1c1d6-c541-4969-af5c-f2611916e576
-- title:
--   Hypergraph: edge Distance eq finite
-- statement:
--   The Hypergraph construction uses the edge Distance eq finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2110-L2151
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2110-L2151

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.edgeDistance_eq_finite (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f : ℕ} (he : e ∈ H.edges) (hf : f ∈ H.edges) :
    H.edgeDistance x e f = H.finiteEdgeDistance e f x := by sorry
