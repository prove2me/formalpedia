-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:11.614628+00:00
-- url     : https://prove2.me/theorems/8fee1bb1-ba8e-4039-82ed-8289bfb74aec
-- title:
--   Euler edge bound for connected drawn graphs
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. This isolates the Euler and face-counting work from the target. A proof route is to establish Euler’s relation for the drawing, count each edge twice in the face boundary walks, and use the lower bound of three on each face boundary, with connectedness and the vertex-count hypothesis handling degenerate cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
    {W : Type} [Fintype W] [LinearOrder W]
    (G : SimpleGraph W) (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 <= Fintype.card W) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card W := by sorry
