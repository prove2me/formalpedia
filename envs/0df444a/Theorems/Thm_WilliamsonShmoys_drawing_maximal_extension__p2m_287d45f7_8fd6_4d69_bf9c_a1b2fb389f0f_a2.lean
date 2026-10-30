-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_maximal_extension__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
-- name    : WilliamsonShmoys.drawing_maximal_extension__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:13.63491+00:00
-- url     : https://prove2.me/theorems/35c6c6fc-b67e-4f1f-ba3c-130c02702187
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Given a drawable graph, choose a drawable supergraph on the same finite vertex type that is maximal under inclusion and has at least as many edges. The candidate family is nonempty because it contains the original graph, and finiteness permits choosing a member with maximal edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.drawing_maximal_extension__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by sorry
