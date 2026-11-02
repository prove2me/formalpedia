-- Prove2me | Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a4
-- name    : WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:57.539195+00:00
-- url     : https://prove2.me/theorems/896d696c-1e18-4de1-b5bd-ab3d52a97871
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A drawable finite simple graph on at least three vertices has at most 3|V|−6 edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P) :
    (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
      P.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
