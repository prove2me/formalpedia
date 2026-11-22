-- Prove2me | Theorems.Thm_Paper_Hypergraph_induced_vertexDistance_le_two_coverCost
-- name    : Paper.Hypergraph.induced_vertexDistance_le_two_coverCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:53.071196+00:00
-- url     : https://prove2.me/theorems/ea167390-e9b0-4361-b6dc-00cf3343228a
-- title:
--   Hypergraph: induced vertex Distance le two cover Cost
-- statement:
--   The small-cover case can retain an entire connected component.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L157-L173
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L157-L173

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.induced_vertexDistance_le_two_coverCost (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ z ∈ H.vertices, 0 ≤ x z) (Q : Finset ℕ) {u v : ℕ}
    (hu : u ∈ (H.induce Q).vertices) (huv : (H.induce Q).primal.Reachable u v) :
    (H.induce Q).vertexDistance x u v ≤ 2 * H.coverCost x := by sorry
