-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_two_groups_close_maxima_give_small_top_gap
-- name    : StabilityDichotomies.Bijunctive.two_groups_close_maxima_give_small_top_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:30:01.639207+00:00
-- url     : https://prove2.me/theorems/0549fda9-b271-4318-89d5-9f929c85ae8c
-- title:
--   Close maxima of disjoint groups imply a small top gap
-- statement:
--   Let $S,T$ be disjoint nonempty finite sets and $f$ be real-valued on their union. If the maxima of $f$ on $S$ and $T$ differ by at most $r$, then the two largest values of $f$ on $S\cup T$ differ by at most $r$. This is the deterministic order-statistic step used in bounding the probability of violating a retained non-unit clause.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Mathlib
open scoped Classical

theorem StabilityDichotomies.Bijunctive.two_groups_close_maxima_give_small_top_gap {α : Type} [DecidableEq α]
    (s t : Finset α) (hs : s.Nonempty) (ht : t.Nonempty) (hdis : Disjoint s t)
    (f : α → ℝ) (a b : α) (ha : a ∈ s) (hb : b ∈ t)
    (hamax : ∀ k ∈ s, f k ≤ f a) (hbmax : ∀ k ∈ t, f k ≤ f b)
    (r : ℝ) (hab : f a - f b ≤ r) (hba : f b - f a ≤ r) :
    ∃ i ∈ s ∪ t, ∃ j ∈ s ∪ t, i ≠ j ∧
      (∀ k ∈ s ∪ t, f k ≤ f i) ∧
      (∀ k ∈ s ∪ t, k ≠ i → f k ≤ f j) ∧
      f i - f j ≤ r := by
  sorry
