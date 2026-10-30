-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:06.888137+00:00
-- url     : https://prove2.me/theorems/9e7a5396-2787-4caf-938c-608408887b08
-- title:
--   Disconnected planar graphs have a strict edge deficit
-- statement:
--   A disconnected drawable simple graph on at least three vertices has strictly fewer than $3|V|-6$ edges. The proof can sum planar edge bounds over connected components, handling one- and two-vertex components separately; having at least two components makes the total bound strict.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    H.edgeSet.ncard + 6 < 3 * Fintype.card V := by sorry
