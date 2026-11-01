-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_partition_cardinality__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- name    : WilliamsonShmoys.component_bounds_sum_partition_cardinality__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:09.772607+00:00
-- url     : https://prove2.me/theorems/a731231d-505e-4034-89ec-a538bd9426d0
-- title:
--   Cardinality sum for the partition
-- statement:
--   The sum of the sizes of the nonempty parts equals the size of the partitioned finite vertex type, by unique coverage.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum_partition_cardinality__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hnonempty : ∀ s ∈ C, s.Nonempty) :
    (∑ s ∈ C, s.card) = Fintype.card V := by sorry
