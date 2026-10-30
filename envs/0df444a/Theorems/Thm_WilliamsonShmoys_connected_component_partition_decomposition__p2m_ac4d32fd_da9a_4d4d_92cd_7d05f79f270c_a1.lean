-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_decomposition__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
-- name    : WilliamsonShmoys.connected_component_partition_decomposition__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:39.95579+00:00
-- url     : https://prove2.me/theorems/3d84d730-6b0a-4f45-aefe-4257d390e6e6
-- title:
--   Connected-component partition with additive counts
-- statement:
--   The vertex sets of the connected components form a finite partition, each component is nonempty and connected, and the component vertex and induced-edge counts sum to the total counts. The empty graph is covered by the empty partition. A proof can use the equivalence classes of graph connectivity, then show every vertex and edge belongs to exactly one class.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_partition_decomposition__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1 {V : Type} [Fintype V] (H : SimpleGraph V) : ∃ (parts : Finset (Finset V)), (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V ∧ (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard ∧ ∀ s ∈ parts, 1 ≤ Fintype.card {v // v ∈ s} ∧ (H.induce (↑s : Set V)).Connected := by sorry
