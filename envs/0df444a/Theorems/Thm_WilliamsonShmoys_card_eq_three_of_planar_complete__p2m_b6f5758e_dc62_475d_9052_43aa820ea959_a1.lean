-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_eq_three_of_planar_complete__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
-- name    : WilliamsonShmoys.card_eq_three_of_planar_complete__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:08.506594+00:00
-- url     : https://prove2.me/theorems/983ead5b-cd2c-4553-afc9-51fdd9f9214f
-- title:
--   A planar complete graph with at least three vertices has exactly three vertices
-- statement:
--   If a finite complete graph has a crossing-free drawing and at least three vertices, then it has exactly three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.card_eq_three_of_planar_complete__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    Fintype.card V = 3 := by sorry
