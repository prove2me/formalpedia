-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCountLower__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1
-- name    : WilliamsonShmoys.edgeMaximalPlanar_edgeCountLower__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:51.878997+00:00
-- url     : https://prove2.me/theorems/2ea32765-2df8-451e-8e1b-57a01a14aed1
-- title:
--   Lower edge-count bound from maximal planarity
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edgeMaximalPlanar_edgeCountLower__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn N) (hMax : ∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) : 3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
