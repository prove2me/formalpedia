-- Prove2me | Theorems.Thm_Paper_Hypergraph_sum_restrictDemand_cost_le
-- name    : Paper.Hypergraph.sum_restrictDemand_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:13.080762+00:00
-- url     : https://prove2.me/theorems/91d1fcac-c90f-4b2e-abd4-552c81bbf70d
-- title:
--   Hypergraph: sum restrict Demand cost le
-- statement:
--   The cover accounting in Observation 5.12. Each edge meets at most one piece.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L145-L200
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L145-L200

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.sum_restrictDemand_cost_le (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (P : ι → Finset ℕ) (x : ℕ → ℝ)
    (hsep : ∀ e ∈ H.edges, ∀ i ∈ I, ∀ j ∈ I,
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j) :
    (∑ i ∈ I, H.coverCost (restrictDemand x (P i))) ≤ H.coverCost x := by sorry
