-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_accounting__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
-- name    : WilliamsonShmoys.connected_planar_face_accounting__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:39:09.804542+00:00
-- url     : https://prove2.me/theorems/47511710-10d7-4fa3-b764-8eff66fff975
-- title:
--   Euler and face accounting for a connected planar drawing
-- statement:
--   This child supplies the exact numerical facts used by the parent. Its independent proof route is Euler’s formula for the connected plane drawing, together with counting edge incidences along facial walks; each edge is counted twice, and the total facial-walk length is at least three per face for a connected simple graph with at least three vertices. Proving these topological facts is the remaining core obligation after the connected completion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_face_accounting__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
