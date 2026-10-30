-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:48:40.588422+00:00
-- url     : https://prove2.me/theorems/6953b2d1-377a-4f12-a204-4d1226429a63
-- title:
--   A disconnected planar graph has a strict planar supergraph
-- statement:
--   If a graph on at least three vertices has a crossing-free drawing and is disconnected, then it has a strictly larger planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by sorry
