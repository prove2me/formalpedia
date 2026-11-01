-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:55.671409+00:00
-- url     : https://prove2.me/theorems/230ef2ff-d0ad-4b7a-9595-07bea2af44fc
-- title:
--   Simple planar edge bound for connected drawings
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hconn : L.Connected) (hcard : 3 ≤ Fintype.card V) : (letI : DecidableRel L.Adj := Classical.decRel L.Adj; L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
