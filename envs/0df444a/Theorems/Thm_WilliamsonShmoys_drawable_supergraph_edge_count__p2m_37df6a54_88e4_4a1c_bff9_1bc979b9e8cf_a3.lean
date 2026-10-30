-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_count__p2m_37df6a54_88e4_4a1c_bff9_1bc979b9e8cf_a3
-- name    : WilliamsonShmoys.drawable_supergraph_edge_count__p2m_37df6a54_88e4_4a1c_bff9_1bc979b9e8cf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:57:05.485989+00:00
-- url     : https://prove2.me/theorems/66e11127-e304-4e1a-a9bb-8a265d178a1c
-- title:
--   Drawable supergraph with maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.drawable_supergraph_edge_count__p2m_37df6a54_88e4_4a1c_bff9_1bc979b9e8cf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
