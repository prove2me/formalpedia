-- Prove2me | Theorems.Thm_WilliamsonShmoys_add_edge_between_unreachable_vertices_preserving_planar_drawing_34a43dbc_488e_44ec_bac5_5fafefe41c67
-- name    : WilliamsonShmoys.add_edge_between_unreachable_vertices_preserving_planar_drawing_34a43dbc_488e_44ec_bac5_5fafefe41c67
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:16:47.208805+00:00
-- url     : https://prove2.me/theorems/5818614d-0bab-4c9c-8ac7-c4917be5e2a9
-- title:
--   Add an edge between unreachable vertices while preserving a planar drawing
-- statement:
--   Given a finite graph drawing and two unreachable vertices, one can add an edge between them and retain a planar drawing on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.add_edge_between_unreachable_vertices_preserving_planar_drawing_34a43dbc_488e_44ec_bac5_5fafefe41c67
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (u v : V)
    (hUnreachable : ¬ K.Reachable u v)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ ¬ J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn J := by sorry
