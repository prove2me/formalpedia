-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_triangulation
-- name    : WilliamsonShmoys.connected_planar_simple_graph_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:56:34.041521+00:00
-- url     : https://prove2.me/theorems/19b80a2c-1c09-40dd-a8e6-789089df722b
-- title:
--   Triangulate a connected planar simple graph
-- statement:
--   Every connected graph with the supplied crossing-free drawing and at least three vertices can be augmented, on the same vertex set, to a planar simple graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
