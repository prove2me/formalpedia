-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:06.797133+00:00
-- url     : https://prove2.me/theorems/eac4b030-cd26-487c-98af-ec9d769936c5
-- title:
--   Euler edge bound for a connected planar supergraph
-- statement:
--   If a finite simple graph M is a subgraph of a connected graph H with a crossing-free drawing, and there are at least three vertices, then M has at most 3|V|−6 edges. This removes the parent’s edge-counting obligation: prove Euler’s formula for the connected planar drawing, count two edge incidences per face, and use simplicity and at least three vertices to bound face lengths below by three; then use M ≤ H to transfer the edge bound. The size hypothesis is essential to this Euler bound and is preserved explicitly. The parent follows by applying the augmentation child to obtain H and then this bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
