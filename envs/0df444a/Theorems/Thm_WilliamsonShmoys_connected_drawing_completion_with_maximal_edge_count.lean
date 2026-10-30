-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_completion_with_maximal_edge_count
-- name    : WilliamsonShmoys.connected_drawing_completion_with_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:33:08.62912+00:00
-- url     : https://prove2.me/theorems/96e18dc0-fcd2-4f0d-85b5-0dc02d147dce
-- title:
--   Drawable completion with the maximal planar edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertex type with exactly 3|V|−6 edges. This also covers disconnected starting graphs; when there are three vertices, the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_completion_with_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
