-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_edge_bounds__p2m_9fc83de8_0852_4661_9f7b_4eaba74d4214_a2
-- name    : WilliamsonShmoys.connected_planar_supergraph_edge_bounds__p2m_9fc83de8_0852_4661_9f7b_4eaba74d4214_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:19.485409+00:00
-- url     : https://prove2.me/theorems/571daa92-bad4-4408-bc3e-99c45f7406bd
-- title:
--   Connected planar supergraph with edge bounds
-- statement:
--   Given a crossing-free drawing on at least three vertices, there is a connected supergraph on the same vertices whose edge count is at least the original graph’s and satisfies n ≤ m + 2 and m + 6 ≤ 3n. The scope-local classical instances make the finite edge-set cardinalities available for the quantified supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph_edge_bounds__p2m_9fc83de8_0852_4661_9f7b_4eaba74d4214_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel _;
       G ≤ H ∧ H.Connected ∧
       G.edgeFinset.card ≤ H.edgeSet.ncard ∧
       Fintype.card V ≤ H.edgeSet.ncard + 2 ∧
       H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) := by sorry
