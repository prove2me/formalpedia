-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a3
-- name    : WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:05:37.733482+00:00
-- url     : https://prove2.me/theorems/8ebe9775-f6af-4eb7-9344-68ad2c5d7599
-- title:
--   A disconnected drawn graph with at least three vertices has a strictly larger planar supergraph
-- statement:
--   For a finite linearly ordered vertex type with at least three elements, a disconnected graph with a drawing under the exact custom predicate has a planar supergraph on the same vertices with strictly more edges. The cardinality condition excludes the supplied empty-type counterexample and follows from the parent’s hypothesis. This child removes the geometric extension step from the parent. A proof route is to redraw the finite collection of connected components in separated regions and join outer-face vertices of two components by a new arc; disconnectedness ensures the edge is new. The remaining obligation is to formalize this redraw and connecting arc while meeting every clause of `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a3
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hN : HasPlanarDrawingOn N)
    (hDisconnected : ¬ N.Connected) :
    ∃ K : SimpleGraph V, N <= K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card < K.edgeFinset.card) := by sorry
