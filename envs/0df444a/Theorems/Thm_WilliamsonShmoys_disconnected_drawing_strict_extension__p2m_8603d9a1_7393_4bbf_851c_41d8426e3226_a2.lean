-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a2
-- name    : WilliamsonShmoys.disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T01:00:45.20874+00:00
-- url     : https://prove2.me/theorems/19d9aac1-e537-4ac1-b81a-be8185854c9e
-- title:
--   A disconnected planar drawing with at least three vertices has a strict drawable extension
-- statement:
--   A disconnected graph with at least three vertices and a crossing-free drawing has a strict supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ HasPlanarDrawingOn L := by
  sorry
