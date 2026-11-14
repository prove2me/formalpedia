-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_uniform_prefix_deletion_sum_eq_last_edge
-- name    : StabilityDichotomies.Bijunctive.uniform_prefix_deletion_sum_eq_last_edge
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:58:36.007895+00:00
-- url     : https://prove2.me/theorems/a834342d-88fd-44e5-a9b5-cf7af80c0fcc
-- title:
--   Uniform prefix deletion costs equal prefix size times the last-edge cost
-- statement:
--   Let a finite set of positions be uniformly permuted, and let $S$ be a nonempty set of retained positions with distinguished last position $j\in S$. For any real cost depending on the retained image set and the selected element, the sum over permutations and retained positions of the deletion cost equals $|S|$ times the sum over permutations of the cost of deleting the element at $j$. This is the symmetry identity used in the outside-first-mask part of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, outside-mask deletion symmetry.

import Mathlib
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.uniform_prefix_deletion_sum_eq_last_edge {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (j : α) (hj : j ∈ S) (cost : Finset α → α → ℝ) :
    (∑ π : Equiv.Perm α, ∑ i ∈ S, cost (S.image π) (π i)) =
      S.card * ∑ π : Equiv.Perm α, cost (S.image π) (π j) := by
  sorry
