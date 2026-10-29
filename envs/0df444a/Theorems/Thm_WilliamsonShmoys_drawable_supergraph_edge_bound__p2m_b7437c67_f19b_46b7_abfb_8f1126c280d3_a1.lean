-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_bound__p2m_b7437c67_f19b_46b7_abfb_8f1126c280d3_a1
-- name    : WilliamsonShmoys.drawable_supergraph_edge_bound__p2m_b7437c67_f19b_46b7_abfb_8f1126c280d3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:00:51.732877+00:00
-- url     : https://prove2.me/theorems/b2793381-3dc8-4ae5-ab06-93034309e127
-- title:
--   Drawable supergraph with the planar edge lower bound
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_edge_bound__p2m_b7437c67_f19b_46b7_abfb_8f1126c280d3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
