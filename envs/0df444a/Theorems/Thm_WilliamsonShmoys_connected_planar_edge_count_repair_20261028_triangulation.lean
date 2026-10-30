-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028_triangulation
-- name    : WilliamsonShmoys.connected_planar_edge_count_repair_20261028_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:55:13.555615+00:00
-- url     : https://prove2.me/theorems/dcb2afb2-ef9b-40e4-8261-e6ef6542b367
-- title:
--   Triangulate a connected planar drawing on the same vertices
-- statement:
--   Every connected simple graph with at least three vertices and a crossing-free drawing can be extended, using the same vertices, to a crossing-free simple graph with exactly 3|V|−6 edges. This is the maximal planar augmentation step; the parent uses only the edge inclusion and edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_repair_20261028_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
