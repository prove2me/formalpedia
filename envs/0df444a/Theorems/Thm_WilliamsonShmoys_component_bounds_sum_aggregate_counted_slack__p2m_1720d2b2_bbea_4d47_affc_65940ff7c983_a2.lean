-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_aggregate_counted_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a2
-- name    : WilliamsonShmoys.component_bounds_sum_aggregate_counted_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:23.803598+00:00
-- url     : https://prove2.me/theorems/c575188a-c998-4798-935c-b2b81c8451d3
-- title:
--   Aggregate slack counted once per part
-- statement:
--   Summing the three-unit slack inequality over all parts, then using the edge-count identity and the partition cardinality sum, bounds the total edge count plus three times the number of parts by three times the total number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum_aggregate_counted_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hsum : (∑ s ∈ C, s.card) = Fintype.card V)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hcomponent : ∀ s ∈ C,
      (N.induce (s : Set V)).edgeFinset.card + 3 ≤ 3 * s.card) :
    N.edgeFinset.card + 3 * C.card ≤ 3 * Fintype.card V := by sorry
