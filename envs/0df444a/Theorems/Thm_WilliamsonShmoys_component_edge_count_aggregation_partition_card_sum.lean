-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_partition_card_sum
-- name    : WilliamsonShmoys.component_edge_count_aggregation_partition_card_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:27:49.581009+00:00
-- url     : https://prove2.me/theorems/f4348491-41d2-4068-94d7-88fbce08768c
-- title:
--   Sum of part sizes equals the vertex count
-- statement:
--   For a finite family of nonempty parts in which every vertex belongs to exactly one part, the sum of the part sizes is the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_count_aggregation_partition_card_sum
    (V : Type) [Fintype V]
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) :
    C.sum Finset.card = Fintype.card V := by sorry
