-- Prove2me | Theorems.Thm_WeightedMajority_Shattered_lemma_7_1
-- name    : WeightedMajority.Shattered.lemma_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:01.04093+00:00
-- url     : https://prove2.me/theorems/9ebcadc9-8c58-40c8-ab89-f6518f3d25a4
-- title:
--   Lemma 7.1 — a prefix realizes an integral target sum
-- statement:
--   Let $r_1,\ldots,r_n$ be positive real numbers, where $n\ge1$, such that each adjacent quotient $r_i/r_{i+1}$ is an integer. If $s>0$, $s\le\sum_{i=1}^n r_i$, and $s/r_1$ is an integer, then some prefix of the list has sum exactly $s$:
--
--   $$
--   \exists m\le n,\qquad \sum_{i=1}^{m}r_i=s.
--   $$
--
--   This arithmetic lemma is used to select an exact weight total in the next lemma.
--
--   **Formalization Note** Lean numbers the $n$ entries from zero, so $r_1$ is `r 0`. The explicit $n\ge1$ makes the source's $r_1$ well-defined.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 244, Lemma 7.1; https://doi.org/10.1006/inco.1994.1009

import Mathlib

namespace WeightedMajority.Shattered

/-- Littlestone--Warmuth, Lemma 7.1, p. 244. The book's indices 1,...,n are
represented by `Fin n`, starting at zero. -/
theorem lemma_7_1 {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (hquot : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
      ∃ k : ℤ, r i / r j = (k : ℝ))
    (s : ℝ) (hspos : 0 < s) (hsle : s ≤ ∑ i, r i)
    (hsint : ∃ k : ℤ, s / r ⟨0, hn⟩ = (k : ℝ)) :
    ∃ m : ℕ, m ≤ n ∧ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), r i = s := by sorry

end WeightedMajority.Shattered
