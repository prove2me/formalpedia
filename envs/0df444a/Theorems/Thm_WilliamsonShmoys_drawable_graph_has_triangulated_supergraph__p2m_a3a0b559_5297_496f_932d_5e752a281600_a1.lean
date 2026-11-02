-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph__p2m_a3a0b559_5297_496f_932d_5e752a281600_a1
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_a3a0b559_5297_496f_932d_5e752a281600_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:33:07.960778+00:00
-- url     : https://prove2.me/theorems/9a3366a6-4a3c-4f33-8539-99f470118709
-- title:
--   Triangulated drawable supergraph on the same vertices
-- statement:
--   Every graph with the given planar drawing on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_a3a0b559_5297_496f_932d_5e752a281600_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (dL : DecidableRel L.Adj) (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V) : ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj), L <= M ∧ HasPlanarDrawingOn M ∧ M.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
