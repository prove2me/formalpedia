-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_step_of_three_vertices_add_planar_edge
-- name    : WilliamsonShmoys.connected_step_of_three_vertices_add_planar_edge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:24:57.960434+00:00
-- url     : https://prove2.me/theorems/80dabbbc-9d8d-43a8-b554-c184d71f70b7
-- title:
--   Add a planar edge between specified unreachable vertices
-- statement:
--   Given a drawing satisfying `HasPlanarDrawingOn`, two unreachable vertices can be joined by an edge in a planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_step_of_three_vertices_add_planar_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (u v : V)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Adj u v := by sorry
