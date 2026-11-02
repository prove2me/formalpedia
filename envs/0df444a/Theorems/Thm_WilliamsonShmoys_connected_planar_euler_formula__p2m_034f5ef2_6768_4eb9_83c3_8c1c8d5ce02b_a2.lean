-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
-- name    : WilliamsonShmoys.connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:17:07.733984+00:00
-- url     : https://prove2.me/theorems/94c7b079-0fca-49b1-9433-313ce648c245
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   A finite connected graph with a drawing satisfying HasPlanarDrawingOn has a natural face count satisfying Euler’s vertex-edge-face equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by sorry
