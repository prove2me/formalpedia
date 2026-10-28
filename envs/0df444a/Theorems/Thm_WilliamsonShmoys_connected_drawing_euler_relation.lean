-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_relation
-- name    : WilliamsonShmoys.connected_drawing_euler_relation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:52:22.233168+00:00
-- url     : https://prove2.me/theorems/caa64e34-5c3f-409a-8fba-40ceed3c6796
-- title:
--   Euler relation for a connected graph drawing
-- statement:
--   A finite connected simple graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_euler_relation {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
