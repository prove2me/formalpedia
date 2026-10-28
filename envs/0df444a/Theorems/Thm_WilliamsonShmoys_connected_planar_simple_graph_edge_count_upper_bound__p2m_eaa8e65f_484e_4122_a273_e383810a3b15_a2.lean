-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_count_upper_bound__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
-- name    : WilliamsonShmoys.connected_planar_simple_graph_edge_count_upper_bound__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:22:03.472519+00:00
-- url     : https://prove2.me/theorems/facd4f1a-a83c-475e-af46-94d8d3ad5b3d
-- title:
--   Euler edge bound for a connected planar simple graph
-- statement:
--   A connected simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. Its independent proof route is to obtain the faces of the plane embedding, apply Euler’s formula, and count edge incidences around faces; simplicity and the vertex-count hypothesis rule out face boundaries of length below three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_edge_count_upper_bound__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConnected : H.Connected)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
