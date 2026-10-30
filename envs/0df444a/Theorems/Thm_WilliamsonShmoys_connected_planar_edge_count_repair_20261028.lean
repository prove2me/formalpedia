-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028
-- name    : WilliamsonShmoys.connected_planar_edge_count_repair_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:26:18.225889+00:00
-- url     : https://prove2.me/theorems/51153ecc-2cba-4534-b877-a53339ed4e39
-- title:
--   Edge bound for a connected drawable graph
-- statement:
--   This child removes the Euler-counting work from the parent. It is a new formalization of the planar edge-bound argument: extend the connected drawing to a maximal simple planar graph on the same vertices, use that its faces are triangular, count each edge on two face boundaries, and apply Euler’s formula. The proof must connect the exact curve-based drawing predicate to the embedding and face-counting notions used in that argument. The hypothesis of at least three vertices is needed for the stated bound and covers the tight triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_repair_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
