-- Prove2me | Theorems.Thm_Paper_Hypergraph_finite_rooted_tree_decomposition
-- name    : Paper.Hypergraph.finite_rooted_tree_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:13.005097+00:00
-- url     : https://prove2.me/theorems/9dee0773-647c-46ea-90a1-1436022a4cf1
-- title:
--   Hypergraph: finite rooted tree decomposition
-- statement:
--   Reindex a finite tree while retaining its designated root bag.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1251-L1298
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1251-L1298

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.finite_rooted_tree_decomposition (H : Hypergraph) {T : Type*} [Fintype T] [Nonempty T]
    (G : SimpleGraph T) (hG : G.IsTree) (bag : T → Finset ℕ)
    (hsub : ∀ t, bag t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t)
    (hvertex : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t)
    (hrun : ∀ v ∈ H.vertices, (G.induce {t | v ∈ bag t}).Preconnected)
    (root : T) (Z : Finset ℕ) (hroot : Z ⊆ bag root)
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ t, b (bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∃ root, Z ⊆ D.bag root ∧
      ∀ t, b (D.bag t) ≤ r := by sorry
