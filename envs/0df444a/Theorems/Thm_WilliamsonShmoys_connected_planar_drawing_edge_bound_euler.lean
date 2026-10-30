-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_euler
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:04:28.665188+00:00
-- url     : https://prove2.me/theorems/161b188e-83a1-49a4-a950-3b014cb6c657
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the specified crossing-free drawing has at most three times its vertex count minus six edges. Connectivity is expressed by adjacency reachability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : ∀ u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
