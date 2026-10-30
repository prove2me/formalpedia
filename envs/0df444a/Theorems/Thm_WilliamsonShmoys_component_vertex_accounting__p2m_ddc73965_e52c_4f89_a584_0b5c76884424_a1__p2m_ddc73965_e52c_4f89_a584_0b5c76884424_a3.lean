-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_vertex_accounting__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
-- name    : WilliamsonShmoys.component_vertex_accounting__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:01.03064+00:00
-- url     : https://prove2.me/theorems/d7ae0e86-02e7-434a-acfe-3fef1dc883ec
-- title:
--   Component vertex and edge accounting
-- statement:
--   The supports of connected components partition the vertices, and the induced edge sets of those supports partition the graph’s edges. Therefore their vertex and edge cardinalities sum to the corresponding graph counts, and each support is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_vertex_accounting__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [Fintype L.ConnectedComponent] : (Finset.univ.sum fun c : L.ConnectedComponent => (SimpleGraph.ConnectedComponent.supp c).ncard) = Fintype.card V ∧ (Finset.univ.sum fun c : L.ConnectedComponent => (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard) = L.edgeSet.ncard ∧ (∀ c : L.ConnectedComponent, 1 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard) := by sorry
