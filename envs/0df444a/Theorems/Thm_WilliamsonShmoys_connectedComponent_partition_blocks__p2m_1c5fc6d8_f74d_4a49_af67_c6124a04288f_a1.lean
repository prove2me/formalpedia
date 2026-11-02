-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedComponent_partition_blocks__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a1
-- name    : WilliamsonShmoys.connectedComponent_partition_blocks__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:34.678136+00:00
-- url     : https://prove2.me/theorems/4c3146a0-77aa-4966-962e-0fa0c95a3fda
-- title:
--   Connected components give a vertex partition
-- statement:
--   For a finite disconnected graph, produce at least two nonempty, pairwise disjoint blocks covering all vertices, with total block size equal to the vertex count. Each block induces a connected graph, and both ends of every edge lie in a common block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connectedComponent_partition_blocks__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected) :
    (letI : DecidableRel L.Adj := dL;
    ∃ C : Finset (Finset V),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected)) := by sorry
