-- Prove2me | Theorems.Thm_Paper_Hypergraph_edge_in_child
-- name    : Paper.Hypergraph.edge_in_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:11.050287+00:00
-- url     : https://prove2.me/theorems/fdfee9c5-ff95-4cb1-909b-d0f5c069be38
-- title:
--   Hypergraph: edge in child
-- statement:
--   A hyperedge outside the root bag lies in one component together with its boundary.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1759-L1781
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1759-L1781

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.edge_in_child (H : Hypergraph) {W B : Finset ℕ}
    {e : ℕ} (he : e ∈ (H.induce W).edges) (hn : ¬ (H.induce W).edge e ⊆ B) :
    ∃ K ∈ (H.induce (W \ B)).components,
      (H.induce W).edge e ⊆ K ∪ (H.induce W).boundary B K := by sorry
