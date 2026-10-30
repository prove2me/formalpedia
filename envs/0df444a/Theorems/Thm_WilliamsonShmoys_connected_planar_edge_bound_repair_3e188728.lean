-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_repair_3e188728
-- name    : WilliamsonShmoys.connected_planar_edge_bound_repair_3e188728
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:24:19.49705+00:00
-- url     : https://prove2.me/theorems/41c4318d-ce97-4723-a74a-87f78274716c
-- title:
--   Edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing and at least three vertices has at most `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound_repair_3e188728
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hdraw : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
