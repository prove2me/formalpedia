-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_triangulation_maximal_extension
-- name    : WilliamsonShmoys.connected_planar_simple_graph_triangulation_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:02:31.492716+00:00
-- url     : https://prove2.me/theorems/133bf33d-23ce-4932-aabf-ab25d3621b1c
-- title:
--   Extend a connected planar drawing to an edge maximal planar graph
-- statement:
--   Every connected graph with a drawing as specified and at least three vertices has a connected planar supergraph on the same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_triangulation_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
