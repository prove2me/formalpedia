-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_aggregate_parts__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- name    : WilliamsonShmoys.component_bounds_sum_aggregate_parts__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:09.939218+00:00
-- url     : https://prove2.me/theorems/07d89f15-0bc5-48be-8d85-07edd32a1069
-- title:
--   Aggregate the slack across multiple parts
-- statement:
--   If at least two parts partition the vertices and each part satisfies the three-unit slack bound, summing the bounds and using the edge-count identity gives the global bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum_aggregate_parts__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hmany : 2 <= C.card)
    (hsum : (∑ s ∈ C, s.card) = Fintype.card V)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hcomponent : ∀ s ∈ C,
      (N.induce (s : Set V)).edgeFinset.card + 3 <= 3 * s.card) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
