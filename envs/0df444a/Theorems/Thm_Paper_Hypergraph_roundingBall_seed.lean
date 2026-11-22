-- Prove2me | Theorems.Thm_Paper_Hypergraph_roundingBall_seed
-- name    : Paper.Hypergraph.roundingBall_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:52.71516+00:00
-- url     : https://prove2.me/theorems/58d108eb-6ca9-4113-bca4-41c33a14e8f0
-- title:
--   Hypergraph: rounding Ball seed
-- statement:
--   The seed estimate for the repaired cut-off construction.
--   An unweighted shortest path suffices, since only a first exit is needed.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L177-L226
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L177-L226

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.roundingBall_seed (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ z ∈ H.vertices, 0 ≤ x z) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {s q : ℝ}
    (hq : ∀ z ∈ H.vertices ∩ Q, x z ≤ q)
    (hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      s < (H.induce Q).vertexDistance x c v) :
    (s - q) / 2 < H.coverCost (restrictDemand x (H.roundingBall x Q c s)) := by sorry
