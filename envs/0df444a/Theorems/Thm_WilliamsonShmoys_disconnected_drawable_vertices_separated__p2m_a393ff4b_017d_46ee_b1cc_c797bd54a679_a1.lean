-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_vertices_separated__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
-- name    : WilliamsonShmoys.disconnected_drawable_vertices_separated__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T04:20:33.448801+00:00
-- url     : https://prove2.me/theorems/03cc82db-f031-431b-9219-2f5c1b3ca640
-- title:
--   Disconnected graphs have a non-reachable vertex pair
-- statement:
--   A disconnected finite graph has two vertices in different connected components. This uses no drawing hypothesis. The proof follows from connectedness being reachability between every pair; disconnectedness excludes the empty and singleton boundary cases under that definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_drawable_vertices_separated__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdis : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by sorry
