-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_completion__p2m_571daa92_bad4_4408_bc3e_99c45f7406bd_a1
-- name    : WilliamsonShmoys.connected_planar_triangulation_completion__p2m_571daa92_bad4_4408_bc3e_99c45f7406bd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:53:44.904475+00:00
-- url     : https://prove2.me/theorems/8b510604-ecbe-41a0-8ffc-c43a355d8485
-- title:
--   Connected planar triangulation completion
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a connected planar supergraph on the same vertices that still has a crossing-free drawing, contains at least the original edge count, and has exactly 3n−6 edges. The hypothesis n ≥ 3 is needed for the triangulation edge formula and includes the boundary case n = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_triangulation_completion__p2m_571daa92_bad4_4408_bc3e_99c45f7406bd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel _;
       G ≤ H ∧ H.Connected ∧
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       G.edgeFinset.card ≤ H.edgeSet.ncard ∧
       H.edgeSet.ncard = 3 * Fintype.card V - 6) := by sorry
