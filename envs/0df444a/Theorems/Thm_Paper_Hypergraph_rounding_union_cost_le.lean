-- Prove2me | Theorems.Thm_Paper_Hypergraph_rounding_union_cost_le
-- name    : Paper.Hypergraph.rounding_union_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:34.171135+00:00
-- url     : https://prove2.me/theorems/c10733f8-7f13-4a8c-a9a3-440c93844887
-- title:
--   Hypergraph: rounding union cost le
-- statement:
--   Observation 5.13 once the cut-off pieces and their separators are supplied.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L217-L238
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L217-L238

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.rounding_union_cost_le (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (P S : ι → Finset ℕ) {x : ℕ → ℝ} {a A : ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (ha : 0 < a) (hA : 0 ≤ A)
    (hsep : ∀ e ∈ H.edges, ∀ i ∈ I, ∀ j ∈ I,
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j)
    (hcost : ∀ i ∈ I, H.setCoverCost (S i) ≤
      A * a⁻¹ * H.coverCost (restrictDemand x (P i))) :
    H.setCoverCost (H.roundingThreshold x a ∪ I.biUnion S) ≤
      (A + 1) * a⁻¹ * H.coverCost x := by sorry
