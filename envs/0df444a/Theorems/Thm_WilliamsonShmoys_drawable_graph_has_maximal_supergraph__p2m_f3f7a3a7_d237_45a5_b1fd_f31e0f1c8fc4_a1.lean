-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_supergraph__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:50:06.938795+00:00
-- url     : https://prove2.me/theorems/8b8e3425-4aff-41c9-8b9c-234e46d85a56
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex set that has no drawable strict edge supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      ∀ L : SimpleGraph V, J.edgeSet ⊂ L.edgeSet → ¬ HasPlanarDrawingOn L := by sorry
