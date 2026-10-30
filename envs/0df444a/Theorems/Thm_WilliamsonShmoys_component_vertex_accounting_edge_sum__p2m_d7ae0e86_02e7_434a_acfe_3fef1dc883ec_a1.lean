-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_vertex_accounting_edge_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- name    : WilliamsonShmoys.component_vertex_accounting_edge_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:42:59.489212+00:00
-- url     : https://prove2.me/theorems/bea9e6a7-0ad4-4019-b431-579d8a36e318
-- title:
--   Finite edge count by induced components
-- statement:
--   The sum of the edge counts of the graphs induced on component supports equals the original graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_vertex_accounting_edge_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [Fintype L.ConnectedComponent] : (Finset.univ.sum fun c : L.ConnectedComponent => (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard) = L.edgeSet.ncard := by sorry
