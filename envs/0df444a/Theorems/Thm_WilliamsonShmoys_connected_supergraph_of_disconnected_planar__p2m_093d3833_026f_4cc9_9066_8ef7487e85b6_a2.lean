-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
-- name    : WilliamsonShmoys.connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:02:43.583084+00:00
-- url     : https://prove2.me/theorems/b7cc0e50-4117-438e-97b3-add0d92d7fc9
-- title:
--   Connect a disconnected planar drawing by adding edges
-- statement:
--   A disconnected finite simple graph on at least three vertices with a crossing-free drawing can be extended on the same vertex set to a connected simple graph with a crossing-free drawing and at least one additional edge. The proof must preserve the drawing while adding arcs between components through complementary regions; the vertex lower bound and disconnectedness ensure a genuine edge is added.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard + 1 ≤ H.edgeSet.ncard := by sorry
