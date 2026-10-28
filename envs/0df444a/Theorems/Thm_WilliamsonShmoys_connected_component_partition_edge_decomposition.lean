-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_edge_decomposition
-- name    : WilliamsonShmoys.connected_component_partition_edge_decomposition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:32:43.193132+00:00
-- url     : https://prove2.me/theorems/b9156238-b478-43df-9548-65a0131f7231
-- title:
--   Partition vertices into connected components and sum their edges
-- statement:
--   Every finite simple graph admits a partition into nonempty vertex sets whose induced subgraphs are connected, and every edge is counted in exactly one block’s induced edge set. This provides the structural assembly needed by the target. A direct proof route uses graph connectivity classes as blocks, proves the classes partition the finite vertex set, and establishes the edge sum by assigning each edge to the class containing its endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_partition_edge_decomposition
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by sorry
