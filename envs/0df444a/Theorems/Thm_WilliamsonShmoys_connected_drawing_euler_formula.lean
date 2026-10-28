-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_formula
-- name    : WilliamsonShmoys.connected_drawing_euler_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:35:20.685653+00:00
-- url     : https://prove2.me/theorems/199aed23-228a-46be-90af-43c4b0494e84
-- title:
--   Euler vertex-edge-face count for a connected drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, there is a natural number f satisfying the Euler vertex-edge-face count. Here f is the face count represented by the Euler equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_euler_formula
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
