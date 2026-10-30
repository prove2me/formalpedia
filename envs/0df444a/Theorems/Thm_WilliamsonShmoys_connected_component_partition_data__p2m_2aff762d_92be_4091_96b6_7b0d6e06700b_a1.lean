-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
-- name    : WilliamsonShmoys.connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:23.847987+00:00
-- url     : https://prove2.me/theorems/637ed7a6-3035-49c1-aba6-5023ef3aefa9
-- title:
--   Finite connected-component partition data
-- statement:
--   A finite graph's connected components form a partition of its vertices. Their cardinalities sum to the total vertex count, their induced edge counts sum to the graph's edge count, and each induced component is connected. Components with fewer than three vertices have at most card minus one edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) ∧
      Fintype.card V = ∑ W ∈ parts, W.card ∧
      M.edgeSet.ncard = ∑ W ∈ parts, (M.induce (W : Set V)).edgeSet.ncard ∧
      (∀ W ∈ parts, (M.induce (W : Set V)).Connected) ∧
      (∀ W ∈ parts, W.card < 3 →
        (M.induce (W : Set V)).edgeSet.ncard ≤ W.card - 1) := by sorry
