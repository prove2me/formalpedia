-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_face_boundary_bound
-- name    : WilliamsonShmoys.drawingOn_face_boundary_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:34:18.207097+00:00
-- url     : https://prove2.me/theorems/33d64242-310a-491a-b81b-d3f0c8a715bd
-- title:
--   Face-boundary lower bound for a simple planar drawing
-- statement:
--   For the same connected simple graph and drawing, any natural `f` satisfying Euler’s formula obeys the face-boundary inequality. Euler’s equation identifies `f` with the embedding’s face count; the bound follows because every face boundary has length at least three and the total boundary length counts each edge side once, hence totals twice the edge count. Bridges contribute both sides, so they are counted with multiplicity. The `≥3` vertex hypothesis and simplicity exclude degenerate one- and two-edge face boundaries; connectedness is essential to identify the face count using the stated Euler equation. This isolates the boundary-length obligation from the parent. An independent route is to derive the face cycles from the rotation system and show no cycle has length below three: length one would require a loop, and length two would require parallel edges or a connected graph consisting of a single edge, excluded by the hypotheses; then sum cycle lengths over all directed edge sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawingOn_face_boundary_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (f : Nat) (heuler : Fintype.card V + f = G.edgeSet.ncard + 2) : 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
