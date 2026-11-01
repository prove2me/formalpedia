-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_partition_and_edges__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
-- name    : WilliamsonShmoys.component_partition_and_edges__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:09.437209+00:00
-- url     : https://prove2.me/theorems/e69e75b7-a85c-4c30-aae7-c16779d08e89
-- title:
--   Connected induced partition with edge-count decomposition
-- statement:
--   Every finite graph has a partition of its vertices into nonempty sets whose induced subgraphs are connected, and the graph's edge count is the sum of the induced edge counts on those parts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_partition_and_edges__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj) :
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s) ∧
      (∀ s ∈ C, (N.induce (s : Set V)).Connected) ∧
      N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card := by sorry
