-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:01.457289+00:00
-- url     : https://prove2.me/theorems/c508f2ea-079b-4849-b4cc-0b3b748b75aa
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : Nat.le 3 (Fintype.card V)) :
    Nat.le H.edgeFinset.card (3 * Fintype.card V - 6) := by
  sorry
