-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
-- name    : WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:54.855787+00:00
-- url     : https://prove2.me/theorems/76630f91-0f12-4ed5-8e5a-946c2dd877ae
-- title:
--   A disconnected finite graph has an unreachable pair
-- statement:
--   A finite graph with at least two vertices that is not connected has a pair of vertices that are not reachable from one another. The cardinality condition handles the empty and singleton boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hcard : 2 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
