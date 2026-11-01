-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
-- name    : WilliamsonShmoys.connected_planar_euler_face_count__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:56.877289+00:00
-- url     : https://prove2.me/theorems/08370f30-0f8d-4dcb-b430-ba4b2e48e27c
-- title:
--   Natural face count satisfying Euler’s equation
-- statement:
--   A connected graph with the supplied crossing-free drawing has a natural face count satisfying Euler’s equation. This isolates the topological Euler-characteristic obligation from the incidence estimate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_face_count__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by sorry
