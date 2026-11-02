-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:24.681847+00:00
-- url     : https://prove2.me/theorems/182810d1-e6dd-4dca-a527-6379c248c599
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with at least three vertices and the specified crossing-free drawing has at most three times its number of vertices minus six edges. The standard proof uses Euler’s formula and the fact that every face boundary has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconnected : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
