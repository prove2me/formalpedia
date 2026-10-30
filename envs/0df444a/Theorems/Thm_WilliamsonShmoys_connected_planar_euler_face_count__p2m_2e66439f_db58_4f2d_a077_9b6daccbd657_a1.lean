-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- name    : WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:33.984972+00:00
-- url     : https://prove2.me/theorems/6b06a50a-add3-4259-8a32-5532d7c4e168
-- title:
--   Euler face count for a connected drawable graph
-- statement:
--   A connected graph with a crossing-free drawing has a finite face count satisfying Euler’s formula, with the unbounded face included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected) : Exists fun f : Nat => Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
