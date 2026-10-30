-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_degree_sum__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
-- name    : WilliamsonShmoys_connected_planar_face_degree_sum__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:49:20.971983+00:00
-- url     : https://prove2.me/theorems/30cfc9e9-677f-431a-ae7e-f01e3291d489
-- title:
--   Facial degrees for a connected simple plane drawing
-- statement:
--   Given the Euler face count f, the facial walks can be enumerated with degrees at least 3, and their degrees sum to twice the number of edges. Connectedness, simplicity, and at least three vertices are retained because they rule out facial walks of length 1 or 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys_connected_planar_face_degree_sum__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : f + Fintype.card V = G.edgeSet.ncard + 2) :
    ∃ (degrees : Fin f → ℕ),
      (∀ i, 3 ≤ degrees i) ∧
      (∑ i : Fin f, degrees i) = 2 * G.edgeSet.ncard := by sorry
