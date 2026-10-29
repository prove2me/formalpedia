-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a1
-- name    : WilliamsonShmoys.disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T00:39:22.615477+00:00
-- url     : https://prove2.me/theorems/48944e63-c473-444c-8a01-3644001ed62f
-- title:
--   A disconnected planar drawing has a strict drawable extension
-- statement:
--   Any disconnected finite graph with a crossing-free drawing on its ordered vertex type has a strict supergraph on the same vertices that also has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ HasPlanarDrawingOn L := by
  sorry
