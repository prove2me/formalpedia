-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:28:41.500253+00:00
-- url     : https://prove2.me/theorems/ea761ab7-f54e-41d1-973a-d18cf519585a
-- title:
--   Edge bound for a connected drawable simple graph
-- statement:
--   A connected drawable finite simple graph with at least three vertices satisfies the planar Euler edge bound. This supplies the counting step after the first child connects the drawing. A proof route augments the connected drawing to a maximal planar drawing, applies Euler’s formula, and counts face-edge incidences. Connectedness, simplicity, and the lower bound of three vertices are retained for this argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
