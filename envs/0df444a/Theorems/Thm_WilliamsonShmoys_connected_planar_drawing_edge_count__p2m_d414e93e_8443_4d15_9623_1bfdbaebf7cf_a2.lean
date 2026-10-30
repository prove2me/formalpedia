-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:27.103192+00:00
-- url     : https://prove2.me/theorems/f049d633-b05a-453d-95c4-fd4bb4bea31e
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This isolates the topological Euler-formula argument from disconnected-component bookkeeping. A proof route is to obtain a finite plane embedding from the drawing, use Euler's formula, and count edge incidences along face boundaries; simplicity and the size hypothesis rule out facial boundary walks of length below three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
