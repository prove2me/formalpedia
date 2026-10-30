-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
-- name    : WilliamsonShmoys_connected_planar_face_count_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:54:28.462861+00:00
-- url     : https://prove2.me/theorems/9e3e6bde-04d2-450e-851f-2aeb2790307d
-- title:
--   Feasibility bounds for a connected planar face count
-- statement:
--   For a connected simple graph with a crossing-free drawing on at least three vertices, any natural face count satisfying Euler’s equation is positive and is small enough that 2|E| can be written as f integers each at least 3. The connectedness, vertex-count, and drawing hypotheses are retained because they respectively supply the edge lower bound and the planar edge upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys_connected_planar_face_count_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : f + Fintype.card V = G.edgeSet.ncard + 2) :
    0 < f ∧ 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
