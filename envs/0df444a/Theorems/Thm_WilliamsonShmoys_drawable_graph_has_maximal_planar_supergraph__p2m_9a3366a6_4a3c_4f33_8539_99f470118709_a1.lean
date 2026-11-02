-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:14.019596+00:00
-- url     : https://prove2.me/theorems/d747e68f-4b38-43ce-8028-cff46ecd3e2f
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs, when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (dL : DecidableRel L.Adj) (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V) : ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj), L <= M ∧ HasPlanarDrawingOn M ∧ ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N → HasPlanarDrawingOn N → N = M := by sorry
