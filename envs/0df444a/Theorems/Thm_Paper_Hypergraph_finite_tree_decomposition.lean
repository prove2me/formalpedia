-- Prove2me | Theorems.Thm_Paper_Hypergraph_finite_tree_decomposition
-- name    : Paper.Hypergraph.finite_tree_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:38.9338+00:00
-- url     : https://prove2.me/theorems/9b61f332-6ae2-4a2f-9a89-f5bdd842f177
-- title:
--   Hypergraph: finite tree decomposition
-- statement:
--   Reindex a decomposition on any finite nonempty tree to the representation used here.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1301-L1311
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1301-L1311

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.finite_tree_decomposition (H : Hypergraph) {T : Type*} [Fintype T] [Nonempty T]
    (G : SimpleGraph T) (hG : G.IsTree) (bag : T → Finset ℕ)
    (hsub : ∀ t, bag t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t)
    (hvertex : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t)
    (hrun : ∀ v ∈ H.vertices, (G.induce {t | v ∈ bag t}).Preconnected)
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ t, b (bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∀ t, b (D.bag t) ≤ r := by sorry
