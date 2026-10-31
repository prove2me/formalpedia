-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:51.175314+00:00
-- url     : https://prove2.me/theorems/e3346028-5844-4d8e-a324-faf6b25a328d
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing satisfies the six-slack planar edge bound. This is the main remaining mathematical obligation: pass from the drawing to a finite plane embedding, apply Euler’s formula, and count face-boundary incidences. Simplicity and the size hypothesis are needed to rule out facial boundary walks of length below three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
