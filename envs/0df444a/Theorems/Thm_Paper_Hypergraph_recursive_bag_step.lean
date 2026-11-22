-- Prove2me | Theorems.Thm_Paper_Hypergraph_recursive_bag_step
-- name    : Paper.Hypergraph.recursive_bag_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:08.473579+00:00
-- url     : https://prove2.me/theorems/b7f3782e-16cc-4572-8ccf-6df2f7ea667f
-- title:
--   Hypergraph: recursive bag step
-- statement:
--   One step of the recursion, including the inherited boundary invariant.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1628-L1714
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1628-L1714

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.recursive_bag_step (H : Hypergraph) {η r : ℝ} (hη : 0 < η ∧ η < 1)
    (hr : H.sep η < r) {W Z : Finset ℕ} (hW : W ⊆ H.vertices) (hZ : Z ⊆ W)
    (hcost : H.setCoverCost Z ≤ (r + 1) / (1 - η)) {u : ℕ} (hu : u ∈ W \ Z) :
    ∃ B, Z ⊆ B ∧ B ⊆ W ∧ u ∈ B ∧
      H.setCoverCost B ≤ (r + 1) / (1 - η) + r + 1 ∧
      ∀ K ∈ (H.induce (W \ B)).components,
        H.setCoverCost ((H.induce W).boundary B K) ≤ (r + 1) / (1 - η) := by sorry
