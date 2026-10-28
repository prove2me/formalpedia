-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_face_incidence_bound
-- name    : WilliamsonShmoys.connected_drawing_face_incidence_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:02:39.517119+00:00
-- url     : https://prove2.me/theorems/6d1503a1-7a26-4fe3-8538-62de9241bbe9
-- title:
--   Lower bound on face boundary incidences
-- statement:
--   For the face count of a connected simple planar graph with at least three vertices, the total face boundary length is at least three per face and equals twice the number of edges, including repeated edge sides on bridges. Thus three times the face count is at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_face_incidence_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f <= 2 * G.edgeSet.ncard := by sorry
