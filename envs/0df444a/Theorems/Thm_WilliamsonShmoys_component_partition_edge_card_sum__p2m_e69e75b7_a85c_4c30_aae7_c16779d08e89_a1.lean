-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_partition_edge_card_sum__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
-- name    : WilliamsonShmoys.component_partition_edge_card_sum__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:46.262335+00:00
-- url     : https://prove2.me/theorems/5190343c-72fe-4ace-a509-b126bd39e3ca
-- title:
--   Edge count from a closed vertex partition
-- statement:
--   For a finite simple graph, if its vertices partition into parts and every edge has both endpoints in a common part, then the graph's edge count equals the sum of the induced edge counts on those parts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_partition_edge_card_sum__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hclosed : ∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card := by sorry
