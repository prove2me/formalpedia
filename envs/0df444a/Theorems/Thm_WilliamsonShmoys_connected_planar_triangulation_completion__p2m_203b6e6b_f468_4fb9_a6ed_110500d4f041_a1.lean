-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_completion__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
-- name    : WilliamsonShmoys_connected_planar_triangulation_completion__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:13.180747+00:00
-- url     : https://prove2.me/theorems/d5fb2175-2340-4982-8e4d-d8f2c0e58052
-- title:
--   Completion of a connected planar drawing to a triangulation
-- statement:
--   A connected graph with a crossing-free drawing and at least three vertices can be extended, without adding vertices, to a triangulated simple planar graph with exactly $3|V|-6$ edges. This isolates the topological work: repeatedly add noncrossing face diagonals, and use Euler's formula after triangulation. At the three-vertex boundary, the completion is the triangle. The parent combines this exact count with edge-count monotonicity to obtain the required inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_connected_planar_triangulation_completion__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
