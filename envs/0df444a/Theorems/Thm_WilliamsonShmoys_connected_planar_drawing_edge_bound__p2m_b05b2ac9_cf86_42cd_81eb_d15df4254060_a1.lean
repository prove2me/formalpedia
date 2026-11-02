-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:08.171431+00:00
-- url     : https://prove2.me/theorems/1dbaee3e-ce5f-437b-b54c-6804519e37e5
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges. A proof route is Euler’s formula together with a treatment of bridges or an edge-maximal planar extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConn : H.Connected) (hH : HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
