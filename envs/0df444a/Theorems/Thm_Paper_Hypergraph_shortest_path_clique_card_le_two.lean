-- Prove2me | Theorems.Thm_Paper_Hypergraph_shortest_path_clique_card_le_two
-- name    : Paper.Hypergraph.shortest_path_clique_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:24.611798+00:00
-- url     : https://prove2.me/theorems/292f9820-787a-4d0e-8608-ef097fc68d5d
-- title:
--   Hypergraph: shortest path clique card le two
-- statement:
--   A shortest unweighted path contains at most two vertices of any clique.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L22-L53
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L22-L53

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.shortest_path_clique_card_le_two {G : SimpleGraph ℕ} {u v : ℕ}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (S : Finset ℕ)
    (hS : ∀ z ∈ S, z ∈ p.support)
    (hclique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) : S.card ≤ 2 := by sorry
