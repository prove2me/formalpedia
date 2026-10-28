-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension_d974173a
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_extension_d974173a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:41:15.638102+00:00
-- url     : https://prove2.me/theorems/331c0fea-dd04-45c7-8011-2dffa6ea2d8d
-- title:
--   Drawable graphs admit a triangulated extension
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulated_extension_d974173a {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
