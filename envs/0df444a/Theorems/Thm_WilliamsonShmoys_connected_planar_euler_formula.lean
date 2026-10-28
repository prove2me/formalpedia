-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_formula
-- name    : WilliamsonShmoys.connected_planar_euler_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:09:39.63799+00:00
-- url     : https://prove2.me/theorems/c75e86a0-1a93-43e7-88cc-90aa580d65b4
-- title:
--   Euler formula for a connected graph with a planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_formula
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = P.edgeSet.ncard + 2 := by sorry
