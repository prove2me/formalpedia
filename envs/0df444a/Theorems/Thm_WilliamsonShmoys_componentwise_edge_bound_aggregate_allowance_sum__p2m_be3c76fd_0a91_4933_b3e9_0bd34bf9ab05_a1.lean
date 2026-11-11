-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentwise_edge_bound_aggregate_allowance_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- name    : WilliamsonShmoys.componentwise_edge_bound_aggregate_allowance_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:42.264973+00:00
-- url     : https://prove2.me/theorems/7299e588-e2ed-481e-9043-2d583d37a1d6
-- title:
--   Sum component allowances under the global size bound
-- statement:
--   For positive component sizes summing to at least three, the sum of the large-component allowances 3m−6 and the small-component allowances ⌊m/2⌋ is at most 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Algebra.BigOperators.Ring.Nat
set_option autoImplicit false

theorem WilliamsonShmoys.componentwise_edge_bound_aggregate_allowance_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
    {n : Nat} (C : Type) [Fintype C] (m : C → Nat) (hm : ∀ c, 0 < m c)
    (hn : 3 ≤ n) (hsum : (∑ c, m c) = n) :
    (∑ c, if 3 ≤ m c then 3 * m c - 6 else m c / 2) ≤ 3 * n - 6 := by sorry
