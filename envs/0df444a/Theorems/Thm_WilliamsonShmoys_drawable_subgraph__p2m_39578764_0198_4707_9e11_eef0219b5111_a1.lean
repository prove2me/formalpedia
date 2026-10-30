-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_subgraph__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
-- name    : WilliamsonShmoys.drawable_subgraph__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:39.12165+00:00
-- url     : https://prove2.me/theorems/1001afa7-bf35-47f1-8f7a-cbe130056271
-- title:
--   Planar drawing restricts to subgraphs
-- statement:
--   If a graph has a crossing-free drawing, every subgraph has one by reusing the same vertex positions and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_subgraph__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hDraw : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by
  sorry
