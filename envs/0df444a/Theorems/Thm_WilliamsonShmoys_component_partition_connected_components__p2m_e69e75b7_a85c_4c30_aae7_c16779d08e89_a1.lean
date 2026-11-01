-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_partition_connected_components__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
-- name    : WilliamsonShmoys.component_partition_connected_components__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:45.452197+00:00
-- url     : https://prove2.me/theorems/fad8f532-767f-4381-a82f-95059b392e52
-- title:
--   Finite connected-component partition and edge closure
-- statement:
--   Every finite graph's vertices partition into nonempty connected induced parts, and the endpoints of every edge lie in one common part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_partition_connected_components__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj) :
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s) ∧
      (∀ s ∈ C, (N.induce (s : Set V)).Connected) ∧
      (∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) := by sorry
