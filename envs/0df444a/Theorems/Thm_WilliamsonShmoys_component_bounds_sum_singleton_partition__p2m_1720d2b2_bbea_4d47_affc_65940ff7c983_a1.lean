-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_singleton_partition__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- name    : WilliamsonShmoys.component_bounds_sum_singleton_partition__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:13.018666+00:00
-- url     : https://prove2.me/theorems/cead4212-c380-4992-bb07-66f494ce734c
-- title:
--   Handle a one-part partition
-- statement:
--   When the partition has one part, unique coverage and nonemptiness identify that part with the whole vertex set; the local bound then gives the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum_singleton_partition__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hconnected : ∀ s ∈ C, (N.induce (s : Set V)).Connected)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hlocal : ∀ s : Finset V, 3 <= s.card ->
      (N.induce (s : Set V)).Connected ->
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6)
    (hsingle : C.card = 1) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
