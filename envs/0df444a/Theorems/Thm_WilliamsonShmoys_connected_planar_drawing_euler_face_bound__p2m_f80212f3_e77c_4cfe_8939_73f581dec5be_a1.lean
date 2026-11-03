-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_bound__p2m_f80212f3_e77c_4cfe_8939_73f581dec5be_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_bound__p2m_f80212f3_e77c_4cfe_8939_73f581dec5be_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:37:12.220185+00:00
-- url     : https://prove2.me/theorems/0c722b40-f62a-4eb9-8c3e-41b6d8bfbb51
-- title:
--   Euler and face-incidence bounds for a connected planar drawing
-- statement:
--   For a connected finite graph with at least three vertices and the supplied crossing-free drawing, there is a natural number of faces satisfying Euler’s vertex-edge-face count and the lower bound on total face-boundary incidences. This is the substantive topological obligation; it handles bridges by counting facial boundary walks with multiplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_bound__p2m_f80212f3_e77c_4cfe_8939_73f581dec5be_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ,
      Fintype.card V + f = J.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * J.edgeFinset.card := by sorry
