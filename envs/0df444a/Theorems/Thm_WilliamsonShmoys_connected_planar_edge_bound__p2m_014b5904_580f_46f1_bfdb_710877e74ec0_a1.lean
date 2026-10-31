-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:45:22.942262+00:00
-- url     : https://prove2.me/theorems/ab87e506-ebfe-40bd-9284-3be9eecbc974
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected drawable simple graph on at least three vertices has at most 3n − 6 edges. Extract the faces of the drawing, use Euler’s formula, and count edge sides around face boundaries; connectedness, simplicity, and the vertex-count lower bound ensure the face-boundary count gives the required inequality, including when bridges occur.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hGconn : G.Connected) (hG : HasPlanarDrawingOn G) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
