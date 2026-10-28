-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core_boundary
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_boundary
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:59:00.875019+00:00
-- url     : https://prove2.me/theorems/096e804a-01aa-4f4d-8bc7-ad0de8e0d12f
-- title:
--   Facial boundary count for a connected planar drawing
-- statement:
--   For the supplied connected planar drawing, any natural number `f` satisfying Euler’s equation obeys the facial boundary inequality. This separates the edge-side counting work from the parent’s task of finding a face count. A proof route constructs the embedding and facial boundary walks, counts each edge twice across the walks (including both sides of bridges), and proves each walk has length at least three using simplicity and the at-least-three-vertices hypothesis. Together with Euler’s equation this yields the standard planar edge bound. The statement preserves the drawing, connectivity, and size hypotheses needed for these steps.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_boundary
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L)
    (f : ℕ)
    (heuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f ≤ 2 * L.edgeSet.ncard := by sorry
