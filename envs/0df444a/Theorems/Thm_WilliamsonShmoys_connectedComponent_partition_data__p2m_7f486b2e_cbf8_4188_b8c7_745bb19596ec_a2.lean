-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedComponent_partition_data__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- name    : WilliamsonShmoys.connectedComponent_partition_data__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:23.978425+00:00
-- url     : https://prove2.me/theorems/1c5fc6d8-f74d-4a49-af67-c6124a04288f
-- title:
--   Connected component partition and count conservation
-- statement:
--   For a finite disconnected graph, its connected-component vertex sets form a partition with at least two nonempty blocks. The block sizes sum to the total number of vertices; the induced-subgraph edge counts sum to the graph’s edge count; and each induced subgraph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connectedComponent_partition_data__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected) :
    (letI : DecidableRel L.Adj := dL;
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = L.edgeFinset.card ∧
      (∀ s ∈ C, edgeCount s = (L.induce (↑s : Set V)).edgeFinset.card) ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected)) := by sorry
