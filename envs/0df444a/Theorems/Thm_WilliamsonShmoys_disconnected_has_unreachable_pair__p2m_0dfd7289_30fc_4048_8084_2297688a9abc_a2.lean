-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a2
-- name    : WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:46:07.985752+00:00
-- url     : https://prove2.me/theorems/3e9d3f19-33b8-4eeb-b125-99b90cbb34d7
-- title:
--   Disconnectedness with a nonempty vertex set yields an unreachable pair
-- statement:
--   A finite graph with at least three vertices that is not connected has two vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ M.Connected) :
    ∃ u v : V, ¬ M.Reachable u v := by
  sorry
