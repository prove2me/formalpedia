-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:17:37.765279+00:00
-- url     : https://prove2.me/theorems/89f9508a-afd6-4065-9e12-3df1eadb7958
-- title:
--   Edge bound for connected finite planar graphs
-- statement:
--   A connected finite simple graph on at least three vertices with the supplied crossing-free drawing has at most 3|V|−6 edges. A proof route is to construct the plane embedding induced by the drawing, apply Euler’s formula, and bound the sum of face-boundary lengths below by three per face and above by twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConnected : M.Connected) (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
