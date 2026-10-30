-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:02:41.050905+00:00
-- url     : https://prove2.me/theorems/0a6cb8c8-85f4-4527-b550-0c59830e1a8e
-- title:
--   Connected planar edge bound
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The size and connectedness hypotheses exclude the small exceptional cases. An independent route is to derive Euler’s formula from the drawing, use face-boundary counting, and handle small faces using simplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
