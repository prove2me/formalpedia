-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_connected__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- name    : WilliamsonShmoys.edgeMaximalPlanar_connected__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:54.188248+00:00
-- url     : https://prove2.me/theorems/b38e7e0d-55b6-4800-9dde-424996f32dbe
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   An edge-maximal drawable graph with at least three vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanar_connected__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K)
    (hn : 3 ≤ Fintype.card V) :
    K.Connected := by sorry
