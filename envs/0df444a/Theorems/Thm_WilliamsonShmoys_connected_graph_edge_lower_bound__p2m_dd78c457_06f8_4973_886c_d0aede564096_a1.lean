-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_edge_lower_bound__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- name    : WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:32.739242+00:00
-- url     : https://prove2.me/theorems/1c40eb42-c020-4f53-bb65-75f9b46450e8
-- title:
--   Finite connected graph edge lower bound
-- statement:
--   A finite connected simple graph has at least one fewer edge than vertices, by existence of a spanning tree.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 := by sorry
