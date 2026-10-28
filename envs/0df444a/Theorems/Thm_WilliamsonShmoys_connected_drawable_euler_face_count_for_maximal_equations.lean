-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawable_euler_face_count_for_maximal_equations
-- name    : WilliamsonShmoys.connected_drawable_euler_face_count_for_maximal_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:29:20.522893+00:00
-- url     : https://prove2.me/theorems/07854bfb-4798-40a9-819d-79177af0b8f8
-- title:
--   Euler face count for a connected drawable graph in maximal graph counting
-- statement:
--   For a finite connected graph with the given planar drawing, there is a natural number face count satisfying Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawable_euler_face_count_for_maximal_equations {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hConnected : L.Connected) : ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
