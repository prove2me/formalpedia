-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2
-- name    : WilliamsonShmoys.disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:08.6589+00:00
-- url     : https://prove2.me/theorems/9d6795a0-df2a-4cd4-b626-1874c3a84ac3
-- title:
--   Planar extension of a disconnected drawing
-- statement:
--   A disconnected graph on at least three vertices with a crossing-free drawing has a crossing-free supergraph on the same vertices that is not a subgraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ ¬ H ≤ L := by
  sorry
