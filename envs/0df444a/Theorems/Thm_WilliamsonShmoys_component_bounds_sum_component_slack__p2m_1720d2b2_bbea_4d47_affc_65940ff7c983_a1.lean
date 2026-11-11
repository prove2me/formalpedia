-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_component_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- name    : WilliamsonShmoys.component_bounds_sum_component_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:02.912203+00:00
-- url     : https://prove2.me/theorems/b5e4e732-4222-4bc5-b9d2-0efbdba3637d
-- title:
--   Uniform slack for each connected part
-- statement:
--   Every nonempty connected part has at least three units of slack: its induced edge count plus three is at most three times its vertex count. For parts of size one or two this follows from simplicity; larger parts use the supplied local bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum_component_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hconnected : ∀ s ∈ C, (N.induce (s : Set V)).Connected)
    (hlocal : ∀ s : Finset V, 3 <= s.card ->
      (N.induce (s : Set V)).Connected ->
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6) :
    ∀ s ∈ C, (N.induce (s : Set V)).edgeFinset.card + 3 <= 3 * s.card := by sorry
