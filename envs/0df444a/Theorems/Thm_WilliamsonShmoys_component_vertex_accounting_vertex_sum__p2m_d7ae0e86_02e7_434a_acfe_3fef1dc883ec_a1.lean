-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_vertex_accounting_vertex_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- name    : WilliamsonShmoys.component_vertex_accounting_vertex_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:42:53.04867+00:00
-- url     : https://prove2.me/theorems/575ffcf4-fd2d-4cd3-8479-4f3248e728e0
-- title:
--   Finite vertex count by connected components
-- statement:
--   The sum of the finite support cardinalities of all connected components equals the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_vertex_accounting_vertex_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [Fintype L.ConnectedComponent] : (Finset.univ.sum fun c : L.ConnectedComponent => (SimpleGraph.ConnectedComponent.supp c).ncard) = Fintype.card V := by sorry
