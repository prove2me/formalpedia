-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1
-- name    : WilliamsonShmoys.connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:44.051221+00:00
-- url     : https://prove2.me/theorems/e1f0e5cb-88a1-4c02-a6cc-5b5efd64f417
-- title:
--   Edge bound for a connected drawable graph
-- statement:
--   A connected simple graph with a crossing-free drawing on at least three vertices has at most 3n−6 edges. This is the Euler-counting step used by the parent; the parent obtains its bound for G by monotonicity under G ≤ H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
