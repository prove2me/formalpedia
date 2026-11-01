-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_aggregation_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- name    : WilliamsonShmoys.component_aggregation_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:14.047202+00:00
-- url     : https://prove2.me/theorems/0124ef61-9cc1-4caf-b4c0-50d5bcb74723
-- title:
--   Aggregate connected induced-subgraph edge bounds
-- statement:
--   For a finite simple graph with at least three vertices, bounds of 3|S|−6 for every connected induced subgraph on at least three vertices imply the global 3|V|−6 edge bound. This removes the disconnected-graph bookkeeping from the topological lemma. Prove it by partitioning vertices into connected components, applying the premise to components of size at least three, bounding components of size one or two directly, and summing the component edge counts. The total-size hypothesis is needed for the final arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_aggregation_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hcard : 3 ≤ Fintype.card V)
    (hcomp : ∀ S : Finset V, 3 ≤ S.card →
      (U.induce (↑S : Set V)).Connected →
      (letI : DecidableRel (U.induce (↑S : Set V)).Adj := Classical.decRel _
       (U.induce (↑S : Set V)).edgeFinset.card ≤ 3 * S.card - 6)) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
