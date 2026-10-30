-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_has_exact_edge_count_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_has_exact_edge_count_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:11.86452+00:00
-- url     : https://prove2.me/theorems/7c31868e-1a48-4873-9b3b-c3421781b09b
-- title:
--   Triangulate a connected drawable graph
-- statement:
--   A connected drawable finite graph on at least three vertices has a drawable supergraph on the same vertices with exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_has_exact_edge_count_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
