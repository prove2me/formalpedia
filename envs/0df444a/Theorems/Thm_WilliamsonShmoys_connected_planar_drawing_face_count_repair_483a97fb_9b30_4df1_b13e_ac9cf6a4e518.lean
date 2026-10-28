-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- name    : WilliamsonShmoys.connected_planar_drawing_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:16:06.572604+00:00
-- url     : https://prove2.me/theorems/8052fc90-94d2-4e22-8216-d6b183ec5489
-- title:
--   Euler and face-boundary certificate for a connected planar drawing
-- statement:
--   A connected graph with the specified drawing and at least three vertices has a natural-number face count satisfying Euler’s equation and the face-boundary incidence inequality. For a proof route, extract the finite planar map represented by the drawing, apply Euler’s formula, and count incidences. Simplicity and the vertex bound exclude face-boundary walks of length one or two. The route must also cover trees, whose single face has boundary length at least four when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  sorry
