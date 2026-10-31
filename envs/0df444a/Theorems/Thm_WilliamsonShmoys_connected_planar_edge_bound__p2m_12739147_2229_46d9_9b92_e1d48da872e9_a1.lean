-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:34.427413+00:00
-- url     : https://prove2.me/theorems/2c5adea4-d505-4326-974e-37a0f04a34d9
-- title:
--   Edge bound beneath a connected drawable graph
-- statement:
--   A subgraph of a connected drawable simple graph on at least three vertices satisfies the planar edge bound. The parent uses this after the first child supplies a connected drawable supergraph. The proof route is to establish the bound for H using Euler’s formula and the fact that each face of a connected simple planar graph on at least three vertices has boundary length at least three, then use edge-set monotonicity from G ≤ H. This child contains the main Euler-counting obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1 {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hSub : G ≤ H) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
