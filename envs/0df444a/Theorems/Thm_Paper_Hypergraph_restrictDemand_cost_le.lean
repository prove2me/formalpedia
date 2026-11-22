-- Prove2me | Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_le
-- name    : Paper.Hypergraph.restrictDemand_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:15.345413+00:00
-- url     : https://prove2.me/theorems/68b2418f-c118-48d5-9f13-bc9f29099840
-- title:
--   Hypergraph: restrict Demand cost le
-- statement:
--   The Hypergraph construction uses the restrict Demand cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L66-L72
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L66-L72

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.restrictDemand_cost_le (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (A : Finset ℕ) :
    H.coverCost (restrictDemand x A) ≤ H.coverCost x := by sorry
