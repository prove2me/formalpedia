-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:55.340434+00:00
-- url     : https://prove2.me/theorems/00ee0ef8-811a-4a39-b8c0-1ed175b9b4ef
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A finite connected simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3n − 6` edges. This isolates the Euler-formula and face-boundary-counting argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
