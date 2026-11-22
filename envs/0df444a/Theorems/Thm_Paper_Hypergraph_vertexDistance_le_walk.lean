-- Prove2me | Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
-- name    : Paper.Hypergraph.vertexDistance_le_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:49.670463+00:00
-- url     : https://prove2.me/theorems/de95fb9a-5cc0-44e3-bb01-1ebdba33dd83
-- title:
--   Hypergraph: vertex Distance le walk
-- statement:
--   The Hypergraph construction uses the vertex Distance le walk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L17-L27
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L17-L27

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.vertexDistance_le_walk (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices)
    (p : H.primal.Walk u v) :
    H.vertexDistance x u v ≤ ∑ z ∈ p.support.toFinset, x z := by sorry
