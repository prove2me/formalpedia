-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- name    : WilliamsonShmoys.connected_drawing_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:58.150513+00:00
-- url     : https://prove2.me/theorems/31b98941-c8b1-4f52-9a04-555bdc7f0212
-- title:
--   Euler and face-incidence counts for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has a face count satisfying Euler’s equation, with total boundary incidences equal to twice the edge count and at least three incidences per face. Derive the finite plane map from the drawing, apply Euler’s formula, count both sides of each edge, and rule out facial boundary walks of length one or two using simplicity, connectedness, and the vertex bound. This contains the main topological counting obligation without asserting the final edge inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ F B : Nat, Fintype.card V + F = G.edgeSet.ncard + 2 ∧ B = 2 * G.edgeSet.ncard ∧ 3 * F ≤ B := by sorry
