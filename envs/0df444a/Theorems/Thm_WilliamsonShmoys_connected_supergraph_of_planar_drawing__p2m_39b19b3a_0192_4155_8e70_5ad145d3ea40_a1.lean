-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_planar_drawing__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
-- name    : WilliamsonShmoys.connected_supergraph_of_planar_drawing__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:32:10.866283+00:00
-- url     : https://prove2.me/theorems/4bfdbd76-f3f7-4ad4-8b70-8ece73f54193
-- title:
--   Connect a drawn graph without losing planarity
-- statement:
--   Any finite graph with the stated crossing-free drawing has a connected planar supergraph on the same vertices, with no fewer edges. The edge-count inequality is included explicitly for direct use by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_supergraph_of_planar_drawing__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        N.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
