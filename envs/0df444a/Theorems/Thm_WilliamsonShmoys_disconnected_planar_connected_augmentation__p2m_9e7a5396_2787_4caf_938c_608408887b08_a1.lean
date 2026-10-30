-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- name    : WilliamsonShmoys.disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:10.765294+00:00
-- url     : https://prove2.me/theorems/8470bdfe-f75c-45f2-9449-e6bb0fb08f8f
-- title:
--   Connect a disconnected planar drawing by adding edges
-- statement:
--   A disconnected drawable graph on at least three vertices can be extended on the same vertex set to a connected drawable graph with at least one additional edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ H' : SimpleGraph V,
      HasPlanarDrawingOn H' ∧ H'.Connected ∧
      H.edgeSet.ncard + 1 ≤ H'.edgeSet.ncard := by sorry
