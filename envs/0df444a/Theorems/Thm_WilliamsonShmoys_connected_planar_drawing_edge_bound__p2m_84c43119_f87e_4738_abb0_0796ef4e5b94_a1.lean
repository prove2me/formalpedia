-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:40.161856+00:00
-- url     : https://prove2.me/theorems/de817531-bd94-404e-8018-af6b440cc187
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices, a crossing-free drawing implies the planar edge-count upper bound. This is the Euler-counting core: derive a plane embedding from the drawing, use Euler’s formula, and count at least three boundary incidences per face (with bridges counted twice) to obtain 2|E| ≥ 3|F| and hence |E| ≤ 3|V|−6. Simplicity and the vertex lower bound are needed to exclude face-boundary exceptions. This child preserves the target’s quantitative bound and leaves the nontrivial connected planar counting argument explicit.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
