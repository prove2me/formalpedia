-- Prove2me | Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- name    : WilliamsonShmoys.crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:00.29729+00:00
-- url     : https://prove2.me/theorems/833458fe-f209-438f-86e7-1012b8725315
-- title:
--   Simple planar edge bound
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges. This isolates the edge-count bound from the parent. A proof route is to extend the drawing to a maximal planar simple graph, count each face boundary with length at least three, and combine the face-length count with Euler's formula; connectedness and the lower bound n ≥ 3 are retained for those steps. The remaining core obligation is proving the planar extension and face-boundary counts from the given drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
