-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_edge_count_bound
-- name    : WilliamsonShmoys.connected_drawing_edge_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:39:00.483077+00:00
-- url     : https://prove2.me/theorems/1900a061-7754-4717-8cad-cc59aa97e9d8
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hConn : P.Connected)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
