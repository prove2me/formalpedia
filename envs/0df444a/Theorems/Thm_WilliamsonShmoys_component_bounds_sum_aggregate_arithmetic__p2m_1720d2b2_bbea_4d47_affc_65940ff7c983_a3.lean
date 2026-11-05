-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_aggregate_arithmetic__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a3
-- name    : WilliamsonShmoys.component_bounds_sum_aggregate_arithmetic__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:14.932859+00:00
-- url     : https://prove2.me/theorems/5ce8f134-b991-4c99-ac77-77b7e54ee8a7
-- title:
--   Convert aggregate slack to the global edge bound
-- statement:
--   If the aggregate edge bound includes three units of slack per part, there are at least two parts, and the vertex set has at least three elements, then the graph satisfies the global edge bound. The child isolates the final natural-number arithmetic, which can be proved by linear arithmetic from its hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum_aggregate_arithmetic__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hmany : 2 <= C.card)
    (haggregate : N.edgeFinset.card + 3 * C.card <= 3 * Fintype.card V) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
