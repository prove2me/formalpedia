-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentPartition_count__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
-- name    : WilliamsonShmoys.componentPartition_count__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:07:07.78869+00:00
-- url     : https://prove2.me/theorems/cd0aa248-db2b-4301-971b-6317dccc49ef
-- title:
--   Counting blocks in a connected-component partition
-- statement:
--   For a finite graph with at least three vertices, any nonempty disjoint cover by blocks inducing connected subgraphs has at least two blocks if the graph is disconnected, and the sum of the block sizes equals the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.componentPartition_count__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V)
    (C : Finset (Finset V))
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hcover : ∀ v : V, ∃ s ∈ C, v ∈ s)
    (hdisjoint : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hconnected : ∀ s ∈ C, (L.induce (↑s : Set V)).Connected) :
    letI : DecidableRel L.Adj := dL
    2 ≤ C.card ∧ (∑ s ∈ C, s.card) = Fintype.card V := by sorry
