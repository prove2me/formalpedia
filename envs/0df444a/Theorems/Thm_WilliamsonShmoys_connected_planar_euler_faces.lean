-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_faces
-- name    : WilliamsonShmoys.connected_planar_euler_faces
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:30:33.008451+00:00
-- url     : https://prove2.me/theorems/7cf38b66-cc0d-4edb-bf52-6fb574a2027d
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing has a finite face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_euler_faces
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ F : ℕ, Fintype.card V + F = J.edgeSet.ncard + 2 := by sorry
