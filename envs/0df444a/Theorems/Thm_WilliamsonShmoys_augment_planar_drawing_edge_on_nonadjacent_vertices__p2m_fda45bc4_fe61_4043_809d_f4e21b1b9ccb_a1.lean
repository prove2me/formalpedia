-- Prove2me | Theorems.Thm_WilliamsonShmoys_augment_planar_drawing_edge_on_nonadjacent_vertices__p2m_fda45bc4_fe61_4043_809d_f4e21b1b9ccb_a1
-- name    : WilliamsonShmoys.augment_planar_drawing_edge_on_nonadjacent_vertices__p2m_fda45bc4_fe61_4043_809d_f4e21b1b9ccb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:10.471452+00:00
-- url     : https://prove2.me/theorems/68cd1233-a53f-426e-bbe3-bc09db728777
-- title:
--   Add an edge between nonadjacent vertices of a planar drawing
-- statement:
--   For a finite ordered vertex type, if a graph has a crossing-free drawing and two distinct vertices are not adjacent, there is a planar graph on the same vertices that contains the original graph and has an edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.augment_planar_drawing_edge_on_nonadjacent_vertices__p2m_fda45bc4_fe61_4043_809d_f4e21b1b9ccb_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (u v : V) (huv : u ≠ v) (hnotadj : ¬ Y.Adj u v) : ∃ Z : SimpleGraph V, Y.edgeSet ⊆ Z.edgeSet ∧ Z.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
