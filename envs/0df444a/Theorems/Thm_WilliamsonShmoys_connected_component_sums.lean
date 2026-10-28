-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_sums
-- name    : WilliamsonShmoys.connected_component_sums
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:50:59.952982+00:00
-- url     : https://prove2.me/theorems/10fa8419-0050-4a00-970d-d633f739db7c
-- title:
--   Connected components partition vertex and edge counts
-- statement:
--   For a finite simple graph, its connected components form a finite family of vertex subsets. Their cardinalities sum to the number of vertices, their induced edge counts sum to the graph's edge count, and each induced component is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_sums
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) :
    ∃ C : Finset (Finset V),
      (∑ S ∈ C, S.card = Fintype.card V) ∧
      ((L.edgeSet.ncard : Int) = ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int)) ∧
      (∀ S ∈ C, (L.induce S).Connected) := by sorry
