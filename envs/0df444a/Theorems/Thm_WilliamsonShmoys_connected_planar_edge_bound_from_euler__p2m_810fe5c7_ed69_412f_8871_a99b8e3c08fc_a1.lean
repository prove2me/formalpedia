-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_from_euler__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound_from_euler__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:17.630267+00:00
-- url     : https://prove2.me/theorems/64a468bf-7449-4dff-8ab0-8bb8c0a06a4e
-- title:
--   Connected planar graph edge bound from Euler counting
-- statement:
--   Every connected finite simple graph on at least three vertices with a drawing satisfying HasPlanarDrawingOn has at most 3|V|−6 edges. This isolates the topological Euler-counting case; a proof can extend the drawing to a maximal simple planar drawing and apply Euler's formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_from_euler__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
