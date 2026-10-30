-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- name    : WilliamsonShmoys.connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:33.698798+00:00
-- url     : https://prove2.me/theorems/ac4d32fd-da9a-4d4d-92cd-7d05f79f270c
-- title:
--   Partition into connected pieces with local edge deficits
-- statement:
--   Construct a finite partition of the vertices into nonempty connected induced subgraphs. Their vertex counts and induced edge counts sum to the corresponding graph counts. Large components inherit the deficit-6 inequality from the hypothesis; simplicity supplies a deficit of at least 3 for components of size one or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hBound : ∀ (s : Finset V), (H.induce (↑s : Set V)).Connected → 3 ≤ Fintype.card {v // v ∈ s} → (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s}) : ∃ (parts : Finset (Finset V)), (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V ∧ (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard ∧ ∀ s ∈ parts, 1 ≤ Fintype.card {v // v ∈ s} ∧ (H.induce (↑s : Set V)).Connected ∧ (H.induce (↑s : Set V)).edgeSet.ncard + (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤ 3 * Fintype.card {v // v ∈ s} := by sorry
