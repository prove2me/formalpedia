-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_adds_edge_for_unreachable_vertices__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a1
-- name    : WilliamsonShmoys.disconnected_planar_drawing_adds_edge_for_unreachable_vertices__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:54:17.394843+00:00
-- url     : https://prove2.me/theorems/15da0770-e3a8-4254-a232-e3dedad6c114
-- title:
--   Add an edge between unreachable vertices in a planar drawing
-- statement:
--   Given a planar drawing of a finite ordered graph and two vertices that are not connected by a path, there is a planar supergraph on the same vertices that contains the edge between them and is strictly larger than the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_drawing_adds_edge_for_unreachable_vertices__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hunreachable : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ K.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
