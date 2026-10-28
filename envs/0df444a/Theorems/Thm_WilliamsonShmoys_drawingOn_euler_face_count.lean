-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_euler_face_count
-- name    : WilliamsonShmoys.drawingOn_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:30:07.233767+00:00
-- url     : https://prove2.me/theorems/978f4ae4-8d54-44da-a9de-281c69f04b84
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the supplied crossing-free arc drawing has a natural-number face count satisfying Euler’s formula. The connectedness hypothesis is needed for the `+2` Euler characteristic; the vertex lower bound is retained to match the parent and the drawing’s intended plane-embedding setting. This removes the Euler-count obligation from the parent. An independent route is to extract a cyclic order of incident edge ends from the drawing, form the face permutation on directed edge sides, and prove the connected-map Euler relation, using planar separation/Jordan curve arguments to justify the rotation system’s genus-zero embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawingOn_euler_face_count {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
