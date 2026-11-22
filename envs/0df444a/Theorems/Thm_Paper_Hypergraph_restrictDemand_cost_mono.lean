-- Prove2me | Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_mono
-- name    : Paper.Hypergraph.restrictDemand_cost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:39.312975+00:00
-- url     : https://prove2.me/theorems/dc50a289-153f-4e1c-b7e8-98d684585450
-- title:
--   Hypergraph: restrict Demand cost mono
-- statement:
--   A demand restricted to a smaller vertex set has no larger cover cost.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L56-L64
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L56-L64

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.restrictDemand_cost_mono (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {A B : Finset ℕ} (hAB : A ⊆ B) :
    H.coverCost (restrictDemand x A) ≤ H.coverCost (restrictDemand x B) := by sorry
