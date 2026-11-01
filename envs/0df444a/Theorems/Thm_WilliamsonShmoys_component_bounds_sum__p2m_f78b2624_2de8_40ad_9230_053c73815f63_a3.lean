-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
-- name    : WilliamsonShmoys.component_bounds_sum__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:10.523695+00:00
-- url     : https://prove2.me/theorems/1720d2b2-bbea-4d47-affc-65940ff7c983
-- title:
--   Sum connected-part edge bounds
-- statement:
--   For a finite vertex partition into nonempty connected induced subgraphs whose edge counts sum to the graph's edge count, the local bounds on parts of size at least three imply the global bound when the graph has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_sum__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hconnected : ∀ s ∈ C, (N.induce (s : Set V)).Connected)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
