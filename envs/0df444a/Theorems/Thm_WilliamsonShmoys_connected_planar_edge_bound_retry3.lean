-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_retry3
-- name    : WilliamsonShmoys.connected_planar_edge_bound_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:43:12.564702+00:00
-- url     : https://prove2.me/theorems/1906fed7-9587-4272-aa13-d959c78f2f3e
-- title:
--   Euler edge bound for a connected drawable simple graph
-- statement:
--   A connected simple graph with the supplied planar drawing and at least three vertices has at most 3|V|−6 edges. Prove this by deriving Euler’s formula for the embedding and counting face-edge incidences, using that facial boundary walks have length at least three under these hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
