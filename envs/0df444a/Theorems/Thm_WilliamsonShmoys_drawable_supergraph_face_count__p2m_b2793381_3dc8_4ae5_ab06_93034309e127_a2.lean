-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_face_count__p2m_b2793381_3dc8_4ae5_ab06_93034309e127_a2
-- name    : WilliamsonShmoys.drawable_supergraph_face_count__p2m_b2793381_3dc8_4ae5_ab06_93034309e127_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:23:14.408501+00:00
-- url     : https://prove2.me/theorems/37df6a54-88e4-4a1c-bff9-1bc979b9e8cf
-- title:
--   Drawable supergraph with Euler and triangular-face counts
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices whose number of faces satisfies Euler’s equation and whose faces have three edge incidences each. A proof can choose a maximal drawable supergraph, show each face is triangular, then apply Euler’s formula and count edge-face incidences. The face count implies the parent edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.drawable_supergraph_face_count__p2m_b2793381_3dc8_4ae5_ab06_93034309e127_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∃ f : ℕ,
        Fintype.card V + f = L.edgeSet.ncard + 2 ∧
        3 * f = 2 * L.edgeSet.ncard := by sorry
