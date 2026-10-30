-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_fddd844c
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound_fddd844c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:42:48.024194+00:00
-- url     : https://prove2.me/theorems/d2113679-7a71-4032-9a7c-bf81246b4b4a
-- title:
--   Connected planar edge-count bound
-- statement:
--   A finite simple graph with a crossing-free drawing is bounded by three times its vertex count minus six edges when every pair of vertices is joined by a walk and there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_bound_fddd844c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hConn : ∀ u v, Nonempty (M.Walk u v))
    (hCard : 3 ≤ Fintype.card V) :
    (M.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
