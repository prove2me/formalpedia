-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_retry2_triangulation_extension
-- name    : WilliamsonShmoys.connected_planar_edge_bound_retry2_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:42:09.019744+00:00
-- url     : https://prove2.me/theorems/a73fb191-c28e-4a3b-bff0-3762970c9326
-- title:
--   Same-vertex maximal planar extension
-- statement:
--   Extend the supplied planar drawing to a maximal planar simple graph on the same vertices, with the original graph as a subgraph and exactly 3|V|−6 edges. The size and connectedness hypotheses support triangulation without adding vertices. This is the main topological obligation: add noncrossing edges until every face is triangular, then use Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_retry2_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
