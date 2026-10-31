-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_of_subgraph__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
-- name    : WilliamsonShmoys.drawing_of_subgraph__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:11.784787+00:00
-- url     : https://prove2.me/theorems/1512e18c-0486-4bff-8ace-1728a855dc3e
-- title:
--   Drawability is hereditary under edge deletion
-- statement:
--   A graph whose edges are a subset of a drawable graph’s edges is drawable using the same vertex locations and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_of_subgraph__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H G : SimpleGraph V)
    (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
