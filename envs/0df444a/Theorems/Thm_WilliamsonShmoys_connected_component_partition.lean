-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition
-- name    : WilliamsonShmoys.connected_component_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:47:06.697899+00:00
-- url     : https://prove2.me/theorems/68d0dc03-9ce9-447f-98d4-bae6652bf402
-- title:
--   Partition a finite graph into connected induced blocks
-- statement:
--   The connected components of a finite simple graph form a partition into connected induced blocks, contain every edge within one block, and satisfy the stated edge budget whenever a block has fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_partition
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ P : Finset (Finset V),
      (∀ v : V, ∃! S : Finset V, S ∈ P ∧ v ∈ S) ∧
      (∀ S : Finset V, S ∈ P → (G.induce (S : Set V)).Connected) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∃ S : Finset V, S ∈ P ∧ u ∈ S ∧ v ∈ S) ∧
      (∀ S : Finset V, S ∈ P → S.card < 3 →
        2 * (G.induce (S : Set V)).edgeSet.ncard ≤ S.card) := by sorry
