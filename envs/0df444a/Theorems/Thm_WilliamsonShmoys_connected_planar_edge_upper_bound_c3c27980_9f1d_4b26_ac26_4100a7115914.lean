-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:35:41.233461+00:00
-- url     : https://prove2.me/theorems/d48fb20f-bc84-441f-900f-efa65cdbe037
-- title:
--   Connected planar graph edge upper bound
-- statement:
--   A connected graph with the given crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRconn : R.Connected)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
