-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
-- name    : WilliamsonShmoys.connected_planar_supergraph__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:00:17.795414+00:00
-- url     : https://prove2.me/theorems/03cdb16c-d4b2-4cf3-b4f1-33da613ee6f7
-- title:
--   Connected planar supergraph preserving vertices and edge count
-- statement:
--   A finite planar graph on at least three vertices has a connected planar supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Connected ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       M.edgeFinset.card <= N.edgeFinset.card) := by sorry
