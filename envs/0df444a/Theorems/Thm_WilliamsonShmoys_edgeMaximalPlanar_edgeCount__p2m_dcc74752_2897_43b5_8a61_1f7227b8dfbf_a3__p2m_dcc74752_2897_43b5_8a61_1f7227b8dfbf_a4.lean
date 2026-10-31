-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
-- name    : WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:34:52.657088+00:00
-- url     : https://prove2.me/theorems/9fa2e1cf-f812-43a2-8937-813b0958a481
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn N) (hMax : ∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) : N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
