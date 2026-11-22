-- Prove2me | Theorems.Thm_Paper_Hypergraph_vertexDistance_le_option
-- name    : Paper.Hypergraph.vertexDistance_le_option
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:23.832712+00:00
-- url     : https://prove2.me/theorems/c0520c70-bc49-443b-b950-a2b52fc0b7dd
-- title:
--   Hypergraph: vertex Distance le option
-- statement:
--   The Hypergraph construction uses the vertex Distance le option property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2101-L2108
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2101-L2108

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.vertexDistance_le_option (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices)
    {r : ℝ} (hr : r ∈ insert 1 {r | ∃ p : H.primal.Walk u v,
      p.IsPath ∧ r = ∑ z ∈ p.support.toFinset, x z}) : H.vertexDistance x u v ≤ r := by sorry
