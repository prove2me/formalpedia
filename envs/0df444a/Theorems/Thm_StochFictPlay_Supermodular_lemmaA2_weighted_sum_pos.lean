-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_lemmaA2_weighted_sum_pos
-- name    : StochFictPlay.Supermodular.lemmaA2_weighted_sum_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:55.27169+00:00
-- url     : https://prove2.me/theorems/4a7307ce-4008-4fdc-878b-81242836baa0
-- title:
--   Lemma A.2 — increasing weights against nonpositive partial sums give a positive weighted sum
-- statement:
--   Let $b_1 < b_2 < \dots < b_n$ be a strictly increasing sequence of reals and let $c_1, \dots, c_n$ be reals satisfying condition (13):
--   $$\sum_{k=1}^{j} c_k \le 0 \ \text{ for all } j \le n,\ \text{ with strict inequality for some } j \text{ and equality at } j = n.$$
--   Then
--   $$\sum_{k=1}^{n} b_k c_k > 0.$$
--
--   This summation-by-parts fact is what converts stochastic dominance into strict increasing differences in the proof of Theorem 5.1.
--
--   **Formalization Note** Indices are 0-based; the partial sum $\sum_{k=1}^j c_k$ is the sum over indices below $j$. The paper prints the conclusion as $\sum_{i=1}^n b_k c_k$, a typographical slip for $\sum_{k=1}^n b_k c_k$, which is what is stated.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 28, Lemma A.2 and condition (13)

import Mathlib

namespace StochFictPlay.Supermodular

/-- Lemma A.2 (Hofbauer–Sandholm 2002, manuscript p. 28). Let `b₁ < b₂ < … < bₙ` be strictly
increasing and let `c₁, …, cₙ` satisfy condition (13): every partial sum `∑_{k ≤ j} c_k` is
`≤ 0`, at least one is `< 0`, and the full sum is `0`. Then `∑_k b_k c_k > 0`.
Indices are 0-based: the partial sum `∑_{k=1}^{j} c_k` is the sum over `k.val < j`. The page
prints the conclusion as `∑_{i=1}^{n} b_k c_k`, a slip for `∑_{k=1}^{n}`; the corrected sum is
stated. -/
theorem lemmaA2_weighted_sum_pos (n : ℕ) (b c : Fin n → ℝ) (hb : StrictMono b)
    (hc_le : ∀ j : ℕ, j ≤ n → ∑ k : Fin n, (if k.val < j then c k else 0) ≤ 0)
    (hc_lt : ∃ j : ℕ, j ≤ n ∧ ∑ k : Fin n, (if k.val < j then c k else 0) < 0)
    (hc_eq : ∑ k : Fin n, c k = 0) :
    0 < ∑ k : Fin n, b k * c k := by sorry

end StochFictPlay.Supermodular
