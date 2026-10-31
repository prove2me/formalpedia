-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_maximal_extension__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
-- name    : WilliamsonShmoys.drawable_graph_maximal_extension__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:04.34955+00:00
-- url     : https://prove2.me/theorems/d9b65563-0a68-4c93-ab37-57530a2d0f13
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph that is maximal among drawable supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_maximal_extension__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      L ≤ H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) := by sorry
