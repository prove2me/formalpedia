-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:59.933447+00:00
-- url     : https://prove2.me/theorems/cfd012c7-8a6d-483e-9797-29a733a7d0a7
-- title:
--   Connected planar graph edge bound
-- statement:
--   A connected graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges. Its proof route uses Euler’s formula and counts the edge incidences along face boundaries; simplicity and the size bound ensure each face has boundary length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
