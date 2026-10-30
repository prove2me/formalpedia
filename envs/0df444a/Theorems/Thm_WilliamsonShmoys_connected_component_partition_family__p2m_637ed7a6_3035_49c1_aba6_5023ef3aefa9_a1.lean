-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- name    : WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:39.058768+00:00
-- url     : https://prove2.me/theorems/94e5824a-c757-4689-bf4f-99cc2f2adc56
-- title:
--   Connected components form a finite vertex partition
-- statement:
--   The connected components of a finite simple graph give a unique finite part containing each vertex, their cardinalities sum to the number of vertices, their induced subgraphs are connected, and every edge has both endpoints in one part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) ∧
      Fintype.card V = ∑ W ∈ parts, W.card ∧
      (∀ W ∈ parts, (M.induce (W : Set V)).Connected) ∧
      (∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) := by sorry
