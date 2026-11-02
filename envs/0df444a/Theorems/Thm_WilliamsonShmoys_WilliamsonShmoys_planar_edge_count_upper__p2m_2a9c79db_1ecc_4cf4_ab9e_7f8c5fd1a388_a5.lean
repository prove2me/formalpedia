-- Prove2me | Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_planar_edge_count_upper__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
-- name    : WilliamsonShmoys.WilliamsonShmoys_planar_edge_count_upper__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:37.082228+00:00
-- url     : https://prove2.me/theorems/6024654d-8010-41aa-81f6-d8a205d7f75f
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most 3|V|−6 edges. This packages the general planar upper-bound work, including disconnected graphs, and removes it from the parent. A proof route is to establish the planar Euler bound for connected components and count face-edge incidences, combining the component bounds while preserving the at-least-three-vertices condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.WilliamsonShmoys_planar_edge_count_upper__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
