-- Prove2me | Theorems.Thm_Paper_Hypergraph_vertexDistance_step
-- name    : Paper.Hypergraph.vertexDistance_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:08.322371+00:00
-- url     : https://prove2.me/theorems/64de8f2b-87c3-45a2-9605-910434125b8f
-- title:
--   Hypergraph: vertex Distance step
-- statement:
--   The Hypergraph construction uses the vertex Distance step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L34-L52
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L34-L52

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.vertexDistance_step (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {c u v : ℕ}
    (hc : c ∈ H.vertices) (hv : v ∈ H.vertices) (huv : H.primal.Adj u v) :
    H.vertexDistance x c v ≤ H.vertexDistance x c u + x v := by sorry
