-- Prove2me | Theorems.Thm_Paper_Hypergraph_roundingBall_no_crossing_edge
-- name    : Paper.Hypergraph.roundingBall_no_crossing_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:51.5398+00:00
-- url     : https://prove2.me/theorems/7b9bb395-6b89-48d9-aab7-e8b7f685d9be
-- title:
--   Hypergraph: rounding Ball no crossing edge
-- statement:
--   Adjacent vertices cannot jump across a gap exceeding every vertex demand.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L65-L94
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L65-L94

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.roundingBall_no_crossing_edge (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {s g q : ℝ} (hqg : q < g)
    (hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q) {e : ℕ} (he : e ∈ H.edges) :
    Disjoint (H.edge e) (H.roundingBall x Q c s) ∨
      Disjoint (H.edge e) ((H.vertices ∩ Q) \ H.roundingBall x Q c (s + g)) := by sorry
