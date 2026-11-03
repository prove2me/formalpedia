-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_planar__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
-- name    : WilliamsonShmoys.connected_planar_supergraph_of_planar__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:27.817068+00:00
-- url     : https://prove2.me/theorems/5e2222c4-0636-4642-8636-c52ca7aa8258
-- title:
--   Complete a planar graph to a connected planar supergraph
-- statement:
--   Every finite planar graph under the stated drawing convention has a connected planar supergraph on the same vertex type, obtained by adding edges between its components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph_of_planar__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
