-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_009c4248_3452_48fd_902a_fcf77cc64290_a3
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper__p2m_009c4248_3452_48fd_902a_fcf77cc64290_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:02:54.152977+00:00
-- url     : https://prove2.me/theorems/850da8c6-c17f-44b4-bf50-45ea4566645c
-- title:
--   Connected planar graph edge-count upper bound
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The size hypothesis matters: it permits the face-boundary argument for a connected simple plane graph and includes the tight triangle case. Prove this by deriving Euler’s formula for the embedding determined by the drawing, then counting incidences between edges and face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_upper__p2m_009c4248_3452_48fd_902a_fcf77cc64290_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
