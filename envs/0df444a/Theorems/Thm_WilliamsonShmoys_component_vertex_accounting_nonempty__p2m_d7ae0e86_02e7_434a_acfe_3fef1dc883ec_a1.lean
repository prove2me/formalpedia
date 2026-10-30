-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_vertex_accounting_nonempty__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- name    : WilliamsonShmoys.component_vertex_accounting_nonempty__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:42:59.497313+00:00
-- url     : https://prove2.me/theorems/aa7b992d-8c21-4026-aa27-dc37bca14b0f
-- title:
--   Connected-component supports are nonempty
-- statement:
--   Every connected component has a nonempty support, hence its support has cardinality at least one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_vertex_accounting_nonempty__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [Fintype L.ConnectedComponent] : ∀ c : L.ConnectedComponent, 1 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard := by sorry
