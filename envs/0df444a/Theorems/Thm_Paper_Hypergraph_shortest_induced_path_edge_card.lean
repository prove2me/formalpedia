-- Prove2me | Theorems.Thm_Paper_Hypergraph_shortest_induced_path_edge_card
-- name    : Paper.Hypergraph.shortest_induced_path_edge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:38.388995+00:00
-- url     : https://prove2.me/theorems/dec7c829-2260-4ee7-ba3b-e02576abafa3
-- title:
--   Hypergraph: shortest induced path edge card
-- statement:
--   The Hypergraph construction uses the shortest induced path edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L142-L154
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L142-L154

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.shortest_induced_path_edge_card (H : Hypergraph) (Q : Finset ℕ) {u v : ℕ}
    (hu : u ∈ (H.induce Q).vertices) (p : (H.induce Q).primal.Walk u v)
    (hp : p.length = (H.induce Q).primal.dist u v) {S : Finset ℕ}
    (hS : ∀ z ∈ S, z ∈ p.support) {e : ℕ} (he : e ∈ H.edges) :
    (S ∩ H.edge e).card ≤ 2 := by sorry
