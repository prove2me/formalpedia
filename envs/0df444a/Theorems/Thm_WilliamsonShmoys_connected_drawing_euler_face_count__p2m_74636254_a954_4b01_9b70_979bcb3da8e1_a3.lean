-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
-- name    : WilliamsonShmoys.connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:02:52.431592+00:00
-- url     : https://prove2.me/theorems/29d715cd-2cf2-4155-a00a-88c02ffdfbb1
-- title:
--   Euler face count for a connected drawing
-- statement:
--   For a finite connected graph with a drawing satisfying the given planar drawing predicate, the number of complementary faces is a natural number satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
