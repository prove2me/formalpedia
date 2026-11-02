-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:39.760025+00:00
-- url     : https://prove2.me/theorems/65b9f3b0-4e49-457f-8ae3-e5dab0f54711
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   A connected finite simple graph with at least three vertices and the specified crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
