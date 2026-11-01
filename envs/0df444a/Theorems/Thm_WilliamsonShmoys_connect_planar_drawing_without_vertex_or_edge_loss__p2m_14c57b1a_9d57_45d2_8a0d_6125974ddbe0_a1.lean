-- Prove2me | Theorems.Thm_WilliamsonShmoys_connect_planar_drawing_without_vertex_or_edge_loss__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
-- name    : WilliamsonShmoys.connect_planar_drawing_without_vertex_or_edge_loss__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:38.052707+00:00
-- url     : https://prove2.me/theorems/40acc02f-4154-4df9-8376-4f021b839dce
-- title:
--   Connect a planar drawing without losing vertices or edges
-- statement:
--   Any finite graph with a crossing-free drawing can be extended on the same vertex type to a connected graph with a crossing-free drawing, while retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connect_planar_drawing_without_vertex_or_edge_loss__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
        L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
