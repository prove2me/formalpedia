-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:37.333128+00:00
-- url     : https://prove2.me/theorems/42c50023-969e-4d67-9641-cde1dc4669ab
-- title:
--   Connected planar simple graph edge bound
-- statement:
--   For the connected case, derive a plane embedding from the drawing, apply Euler’s formula, and count face-boundary incidences. Simplicity and the at-least-three-vertices hypothesis give boundary length at least three for every face. The remaining core obligation is formalizing the embedding, Euler, and face-counting steps for the explicit arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  sorry
