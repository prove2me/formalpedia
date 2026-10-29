-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:26:19.89009+00:00
-- url     : https://prove2.me/theorems/64e88619-0cc1-4e31-a79e-772a30fa7500
-- title:
--   Euler face count from a connected planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s equation. This removes the face-count existence and vertex-edge-face equation from the parent. A proof route is to extract the plane embedding represented by the arcs and prove Euler’s formula, for example by a spanning-tree argument together with the effect of adding each remaining embedded edge. The main remaining work is constructing and reasoning about faces for the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
