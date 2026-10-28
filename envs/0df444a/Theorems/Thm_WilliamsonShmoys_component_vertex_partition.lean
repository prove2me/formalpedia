-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_vertex_partition
-- name    : WilliamsonShmoys.component_vertex_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:43:47.033497+00:00
-- url     : https://prove2.me/theorems/b832551a-5ca5-41ee-a0e6-588c5b59b0be
-- title:
--   Connected-component supports form an edge-respecting vertex partition
-- statement:
--   The supports of the connected components give finitely many nonempty, pairwise disjoint vertex blocks covering all vertices. Every edge has both endpoints in one block, and each block’s induced subgraph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_vertex_partition
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      (∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by sorry
