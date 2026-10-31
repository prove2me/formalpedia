-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_triangulated_extension__p2m_a75193d8_91cd_4f7d_9e03_b4a5195cbe40_a1
-- name    : WilliamsonShmoys.drawable_graph_triangulated_extension__p2m_a75193d8_91cd_4f7d_9e03_b4a5195cbe40_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:55.880571+00:00
-- url     : https://prove2.me/theorems/c603be23-9a74-4dd9-9858-66dd86a4b903
-- title:
--   Extend a drawable graph to an exact-count planar graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_triangulated_extension__p2m_a75193d8_91cd_4f7d_9e03_b4a5195cbe40_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
