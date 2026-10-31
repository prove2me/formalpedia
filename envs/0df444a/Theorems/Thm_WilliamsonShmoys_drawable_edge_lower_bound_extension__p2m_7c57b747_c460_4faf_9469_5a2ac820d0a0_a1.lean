-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_lower_bound_extension__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
-- name    : WilliamsonShmoys.drawable_edge_lower_bound_extension__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:00.73087+00:00
-- url     : https://prove2.me/theorems/53305c1c-f1f1-46ad-95d2-bc47d8044b33
-- title:
--   Drawable extension with the planar lower edge count
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges. This removes the completion and lower-count step from the parent while preserving the same vertices, drawing condition, and size boundary. A proof route is to connect components with noncrossing arcs in the unbounded face, then add noncrossing diagonals until the embedding is triangulated; the resulting simple triangulation has 3|V|−6 edges. When n = 3, the completion is the triangle. The work left in this child is the topological construction for the concrete arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.drawable_edge_lower_bound_extension__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
