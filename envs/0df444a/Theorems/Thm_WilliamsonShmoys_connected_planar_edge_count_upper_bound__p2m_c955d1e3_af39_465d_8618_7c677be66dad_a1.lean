-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:28:42.862616+00:00
-- url     : https://prove2.me/theorems/30506b39-3246-4bbb-be30-1654e491b341
-- title:
--   Connected planar drawing edge-count bound
-- statement:
--   A connected finite simple graph on at least three vertices with a crossing-free drawing has at most 3n−6 edges. This isolates the Euler-formula and face-boundary argument from the parent theorem's disconnected case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hConn : M.Connected)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
