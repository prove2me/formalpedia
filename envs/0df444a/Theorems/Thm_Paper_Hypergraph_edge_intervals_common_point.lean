-- Prove2me | Theorems.Thm_Paper_Hypergraph_edge_intervals_common_point
-- name    : Paper.Hypergraph.edge_intervals_common_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:59.755002+00:00
-- url     : https://prove2.me/theorems/4a163230-fcf6-4e59-8a88-2e8b950c75a7
-- title:
--   Hypergraph: edge intervals common point
-- statement:
--   Observation 4.3 follows by taking the smallest distance on an edge.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L190-L203
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L190-L203

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.edge_intervals_common_point (H : Hypergraph) {x d : ℕ → ℝ}
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e : ℕ} (he : e ∈ H.edges) :
    ∃ q : ℝ, ∀ v ∈ H.edge e, d v - x v ≤ q ∧ q ≤ d v := by sorry
