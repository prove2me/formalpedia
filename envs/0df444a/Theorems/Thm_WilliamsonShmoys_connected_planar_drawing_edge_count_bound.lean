-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:59:38.028352+00:00
-- url     : https://prove2.me/theorems/8575ae1d-620b-40d7-9b25-8ae2db919063
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with a drawing satisfying `HasPlanarDrawingOn` has at most `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hQconn : Q.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    Q.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
