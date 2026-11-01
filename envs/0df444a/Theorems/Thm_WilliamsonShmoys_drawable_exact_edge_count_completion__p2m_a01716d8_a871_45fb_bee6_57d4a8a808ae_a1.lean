-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_exact_edge_count_completion__p2m_a01716d8_a871_45fb_bee6_57d4a8a808ae_a1
-- name    : WilliamsonShmoys.drawable_exact_edge_count_completion__p2m_a01716d8_a871_45fb_bee6_57d4a8a808ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:14.368871+00:00
-- url     : https://prove2.me/theorems/10381148-6b51-4b84-8aa4-8b409082ba4a
-- title:
--   Drawable planar completion with exact maximal edge count
-- statement:
--   Any finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_exact_edge_count_completion__p2m_a01716d8_a871_45fb_bee6_57d4a8a808ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
