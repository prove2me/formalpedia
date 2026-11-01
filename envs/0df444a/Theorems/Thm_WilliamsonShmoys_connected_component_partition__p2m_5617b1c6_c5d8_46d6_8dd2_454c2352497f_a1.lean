-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
-- name    : WilliamsonShmoys.connected_component_partition__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:00.869538+00:00
-- url     : https://prove2.me/theorems/aaa6544b-d68f-4c85-b504-f8764908a143
-- title:
--   Finite connected-component partition
-- statement:
--   For every finite simple graph, produce a finite family of vertex sets that covers all vertices, consists of nonempty pairwise disjoint parts, keeps every edge within a part, and induces a connected graph on each part. The empty graph is handled by the empty family. This removes the graph-theoretic component extraction and its partition properties from the parent; a route is to form reachability equivalence classes and represent them as finsets. Formalizing those classes and their finiteness is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_partition__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v, ∃ C, C ∈ parts ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → C.Nonempty) ∧
      (∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) ∧
      (∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → (M.induce (C : Set V)).Connected) := by
  sorry
