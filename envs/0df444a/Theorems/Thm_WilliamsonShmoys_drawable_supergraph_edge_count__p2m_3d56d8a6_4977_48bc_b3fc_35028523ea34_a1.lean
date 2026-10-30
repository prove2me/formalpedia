-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_count__p2m_3d56d8a6_4977_48bc_b3fc_35028523ea34_a1
-- name    : WilliamsonShmoys.drawable_supergraph_edge_count__p2m_3d56d8a6_4977_48bc_b3fc_35028523ea34_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:38:19.940981+00:00
-- url     : https://prove2.me/theorems/1a5a4a98-d076-4be8-9c0b-d5fb8ab1d149
-- title:
--   Extend a drawable graph to a triangulated supergraph
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices can be extended, on the same vertex set, to a drawable graph with exactly 3n−6 edges. The proof route is to extend the drawing to a triangulation, then derive its edge count from Euler’s formula and face-edge incidence counting. The parent uses the supergraph relation and the target’s maximality hypothesis to bound the original graph’s edge count. The geometric triangulation extension is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_edge_count__p2m_3d56d8a6_4977_48bc_b3fc_35028523ea34_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
