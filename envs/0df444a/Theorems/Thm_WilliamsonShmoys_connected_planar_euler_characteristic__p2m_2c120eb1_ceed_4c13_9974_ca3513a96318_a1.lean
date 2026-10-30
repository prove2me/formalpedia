-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_characteristic__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
-- name    : WilliamsonShmoys.connected_planar_euler_characteristic__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:36.116981+00:00
-- url     : https://prove2.me/theorems/5ece0e5e-30ef-45bb-ae74-62f74d190573
-- title:
--   Euler face count for a connected drawn graph
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_characteristic__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) : ∃ F : ℕ, Fintype.card V + F = H.edgeSet.ncard + 2 := by sorry
