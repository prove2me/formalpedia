-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawingOn_triangulation_edge_count
-- name    : WilliamsonShmoys.connected_planar_drawingOn_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:44:33.427391+00:00
-- url     : https://prove2.me/theorems/391dc665-13f3-483e-96ea-e855a976642c
-- title:
--   Triangulation extension for connected planar drawings
-- statement:
--   Every connected planar drawing on a finite ordered vertex type with at least three vertices extends, on the same vertex set, to a planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawingOn_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    exists L : SimpleGraph V,
      K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
