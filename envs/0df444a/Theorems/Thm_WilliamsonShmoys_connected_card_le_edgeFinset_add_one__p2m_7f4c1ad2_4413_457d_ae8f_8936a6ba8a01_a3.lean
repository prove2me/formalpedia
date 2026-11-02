-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3
-- name    : WilliamsonShmoys.connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:57.655202+00:00
-- url     : https://prove2.me/theorems/50d04863-4b21-465e-b0dd-b832c2a82742
-- title:
--   A finite connected graph has at least one fewer edge than vertices
-- statement:
--   For a finite connected simple graph, the number of vertices is at most one more than the number of edges. This child isolates the graph-counting fact used by the target; it does not depend on a planar drawing. A concrete proof route is to take a spanning tree of the connected graph, use that a finite tree has one fewer edge than vertices, and compare the tree's edge set with the graph's edge set. For a single vertex, the bound reads 1 ≤ 0 + 1. The parent then chooses the natural-number slack by subtraction and closes the equality arithmetically.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeFinset.card + 1 := by sorry
