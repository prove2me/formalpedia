-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a1
-- name    : WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T15:38:10.319488+00:00
-- url     : https://prove2.me/theorems/ee4f4da1-4eca-4a5d-97f7-5a027cad546c
-- title:
--   A disconnected drawn graph has a strictly larger planar supergraph
-- statement:
--   For a finite linearly ordered vertex type, any disconnected graph with a crossing-free drawing has a planar supergraph on the same vertices with strictly more edges. The drawing of the supergraph may be chosen anew.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N) (hDisconnected : ¬ N.Connected) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card < K.edgeFinset.card) := by sorry
