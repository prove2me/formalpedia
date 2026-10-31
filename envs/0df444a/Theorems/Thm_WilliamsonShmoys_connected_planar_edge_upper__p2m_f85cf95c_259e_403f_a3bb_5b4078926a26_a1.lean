-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- name    : WilliamsonShmoys.connected_planar_edge_upper__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:36.293488+00:00
-- url     : https://prove2.me/theorems/cb34eb69-c1b1-45f4-b656-1b9a22fd4b69
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most 3n−6 edges, by Euler’s formula and the lower bound of three on face-boundary lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_upper__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
