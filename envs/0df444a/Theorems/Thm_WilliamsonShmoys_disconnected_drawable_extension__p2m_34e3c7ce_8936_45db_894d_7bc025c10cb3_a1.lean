-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a1
-- name    : WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:29.532335+00:00
-- url     : https://prove2.me/theorems/16d79109-516b-4548-9d9c-d4c10611d537
-- title:
--   A disconnected drawable graph has a drawable strict supergraph
-- statement:
--   Every disconnected graph with a crossing-free drawing on a finite linearly ordered vertex type has a strictly larger drawable graph on the same vertices. The argument joins two components by a new edge. This removes the geometric edge-addition work from the parent; a proof can redraw the component embeddings in separated regions and route a connecting arc through the exterior. The exact construction and preservation of the drawing conditions remain to be proved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
