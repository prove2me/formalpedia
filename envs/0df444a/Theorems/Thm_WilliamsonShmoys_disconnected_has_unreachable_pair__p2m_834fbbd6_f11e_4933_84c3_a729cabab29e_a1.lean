-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
-- name    : WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:12:33.885441+00:00
-- url     : https://prove2.me/theorems/989b9922-f20a-4f94-b900-5e3f6311f51e
-- title:
--   Disconnectedness yields an unreachable pair
-- statement:
--   A disconnected graph on a nonempty finite vertex type has two vertices that are not reachable from one another. The stated cardinality bound ensures nonemptiness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by sorry
