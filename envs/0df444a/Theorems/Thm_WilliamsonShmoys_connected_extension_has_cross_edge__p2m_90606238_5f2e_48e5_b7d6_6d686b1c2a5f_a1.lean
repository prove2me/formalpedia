-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_extension_has_cross_edge__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- name    : WilliamsonShmoys.connected_extension_has_cross_edge__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:57.156694+00:00
-- url     : https://prove2.me/theorems/f77c0f3f-d05f-49d3-89d5-7503ae82f64d
-- title:
--   A connected extension contains an edge across original components
-- statement:
--   If H is connected, extends a disconnected K, and every edge outside K crosses original K components, then H has an edge whose endpoints were unreachable in K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_extension_has_cross_edge__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H) (hHConnected : H.Connected)
    (hNotConnected : ¬ K.Connected)
    (hCross : ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y) :
    ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v := by sorry
