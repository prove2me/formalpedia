-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
-- name    : WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:14.630207+00:00
-- url     : https://prove2.me/theorems/45ca2179-d67f-49cd-b32c-f48cff93b6c1
-- title:
--   Disconnectedness yields an unreachable pair
-- statement:
--   For a finite vertex type with at least three elements, disconnectedness supplies two vertices that are not connected by a path. This separates the graph-theoretic witness extraction from the geometric edge-addition argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by
  sorry
