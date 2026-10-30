-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- name    : WilliamsonShmoys.connected_planar_triangulation__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:03.571068+00:00
-- url     : https://prove2.me/theorems/90a6eb8a-5322-4ab0-9f54-46d0ab83dbd2
-- title:
--   Triangulate a connected planar graph on its vertex set
-- statement:
--   Every connected finite planar graph with at least three vertices has a planar supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_triangulation__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
