-- Prove2me | Theorems.Thm_Paper_Hypergraph_separated_restrictDemand_cost_add_le
-- name    : Paper.Hypergraph.separated_restrictDemand_cost_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:28.448031+00:00
-- url     : https://prove2.me/theorems/916d064a-b095-4180-8ad7-b05300d5a82e
-- title:
--   Hypergraph: separated restrict Demand cost add le
-- statement:
--   Separated sets use disjoint families of covering edges.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L121-L135
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L121-L135

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.separated_restrictDemand_cost_add_le (H : Hypergraph) (x : ℕ → ℝ)
    (A B : Finset ℕ)
    (hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) A ∨ Disjoint (H.edge e) B) :
    H.coverCost (restrictDemand x A) + H.coverCost (restrictDemand x B) ≤
      H.coverCost (restrictDemand x (A ∪ B)) := by sorry
