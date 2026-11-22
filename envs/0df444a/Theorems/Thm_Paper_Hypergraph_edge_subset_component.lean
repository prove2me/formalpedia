-- Prove2me | Theorems.Thm_Paper_Hypergraph_edge_subset_component
-- name    : Paper.Hypergraph.edge_subset_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:49.341446+00:00
-- url     : https://prove2.me/theorems/e42fa17a-97d3-418b-a08e-ed4c30b88569
-- title:
--   Hypergraph: edge subset component
-- statement:
--   The Hypergraph construction uses the edge subset component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1324-L1330
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1324-L1330

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.edge_subset_component (H : Hypergraph) {C : Finset ℕ} (hC : C ∈ H.components)
    {e v : ℕ} (he : e ∈ H.edges) (hve : v ∈ H.edge e) (hvC : v ∈ C) : H.edge e ⊆ C := by sorry
