-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_edge_and_card_sums
-- name    : WilliamsonShmoys.connected_component_partition_edge_and_card_sums
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:27:53.006666+00:00
-- url     : https://prove2.me/theorems/7d15a023-4fc8-4e85-8436-894a73f70672
-- title:
--   Partition a finite graph into connected components and count vertices and edges
-- statement:
--   Every finite simple graph admits a finite partition of its vertices into nonempty sets whose induced subgraphs are connected. The sum of the component sizes is the number of vertices, and the sum of the induced component edge counts is the graph's edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_partition_edge_and_card_sums
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    ∃ comps : Finset (Set V),
      (∀ C ∈ comps, C.Nonempty) ∧
      (∀ C ∈ comps, ∀ D ∈ comps, C ≠ D → Disjoint C D) ∧
      (∀ v : V, ∃ C ∈ comps, v ∈ C) ∧
      (∀ C ∈ comps, (K.induce C).Connected) ∧
      (∑ C ∈ comps, C.ncard = Fintype.card V) ∧
      (K.edgeSet.ncard = ∑ C ∈ comps, (K.induce C).edgeSet.ncard) := by sorry
