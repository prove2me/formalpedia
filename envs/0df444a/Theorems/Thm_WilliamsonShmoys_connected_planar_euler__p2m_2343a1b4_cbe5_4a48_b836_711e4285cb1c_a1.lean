-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
-- name    : WilliamsonShmoys.connected_planar_euler__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:38.395945+00:00
-- url     : https://prove2.me/theorems/58612374-1deb-4852-bf25-cef86ac451da
-- title:
--   Euler equation for a connected graph with a planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, there is a natural-number face count satisfying Euler’s equation: vertices plus faces equal edges plus two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
