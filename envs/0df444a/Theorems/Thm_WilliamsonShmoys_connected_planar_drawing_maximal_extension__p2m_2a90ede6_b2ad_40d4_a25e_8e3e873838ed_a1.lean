-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_maximal_extension__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_maximal_extension__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:49.988312+00:00
-- url     : https://prove2.me/theorems/abbad492-aa2c-464e-8cb6-154e5e3bb3de
-- title:
--   Maximal drawable extension of a connected planar graph
-- statement:
--   Any connected drawable simple graph with at least three vertices has a drawable connected supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_maximal_extension__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hDraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      HasPlanarDrawingOn K ∧
      (∀ u v, Relation.ReflTransGen K.Adj u v) ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) := by sorry
