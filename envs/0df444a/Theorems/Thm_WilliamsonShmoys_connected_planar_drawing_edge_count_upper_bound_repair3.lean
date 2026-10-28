-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_upper_bound_repair3
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count_upper_bound_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:06:32.923492+00:00
-- url     : https://prove2.me/theorems/3bfdd216-0218-4372-98fc-4ac585666340
-- title:
--   Connected planar edge-count upper bound
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This removes the connected planar counting obligation from the parent; a proof route is to extend the drawing to a maximal planar graph, count face-edge incidences, and apply Euler’s formula. The condition |V| ≥ 3 is retained for the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_count_upper_bound_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hconn : T.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
