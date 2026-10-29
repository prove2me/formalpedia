-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:22:55.5951+00:00
-- url     : https://prove2.me/theorems/95790cd1-3c8d-42ec-ac7d-a0a6203907ec
-- title:
--   Euler edge bound for a connected planar graph
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the Euler-counting work from the component bookkeeping.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_upper__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
