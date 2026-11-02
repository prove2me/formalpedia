-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension__p2m_4b104b32_56a0_4b02_b537_5e9d1339dc2d_a2
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_extension__p2m_4b104b32_56a0_4b02_b537_5e9d1339dc2d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:22.720444+00:00
-- url     : https://prove2.me/theorems/3c50d639-b449-4a2f-a283-3dfd9e523102
-- title:
--   Every drawable graph extends to a triangulated drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_triangulated_extension__p2m_4b104b32_56a0_4b02_b537_5e9d1339dc2d_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) [DecidableRel P.Adj] (hcard : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) : ∃ Q : SimpleGraph V, ∃ hQdec : DecidableRel Q.Adj, (letI : DecidableRel Q.Adj := hQdec; P ≤ Q ∧ HasPlanarDrawingOn Q ∧ Q.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
