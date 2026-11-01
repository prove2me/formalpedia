-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_from_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
-- name    : WilliamsonShmoys.connected_planar_supergraph_from_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:08.763011+00:00
-- url     : https://prove2.me/theorems/6c35d7b0-b5ac-47cb-81ba-67341f778754
-- title:
--   Finite maximality turns strict planar extensions into connectivity
-- statement:
--   If every disconnected planar supergraph of G admits a strict planar edge-set extension, then a connected planar supergraph of G exists. Choose an inclusion-maximal edge set among the finitely many candidates; if its graph were disconnected, the extension hypothesis would contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph_from_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hstep : ∀ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊂ L.edgeSet ∧ HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
