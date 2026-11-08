-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_recursion_length_bound
-- name    : QRetrieval.Adaptive.recursion_length_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:18.405866+00:00
-- url     : https://prove2.me/theorems/bf730fe0-137e-42f6-acb6-fb5478bb9794
-- title:
--   Unrolled recursion — $m^{(j)}\le m/p^j+2n\sum_{i<j}p^{-i}\le m/p^j+2n\sqrt2/(\sqrt2-1)$
-- statement:
--   Let $n>0$, $p\ge\sqrt2$ and $m_1\ge 2np$ (Eq. (4)) be real numbers, and let $m^{(0)},\dots,m^{(J)}\ge0$ be the lengths after $j$ applications of the recurrence, with
--
--   $$
--   m^{(j+1)}\le 2n\Bigl(\frac{m^{(j)}}{m_1}+1\Bigr)\qquad(0\le j<J).
--   $$
--
--   Then
--
--   1. $m^{(j+1)}\le \dfrac{m^{(j)}}{p}+2n$ for every $j<J$;
--   2. for every $j\le J$,
--   $$
--   m^{(j)}\ \le\ \frac{m^{(0)}}{p^j}+2n\sum_{i=0}^{j-1}p^{-i}\ \le\ \frac{m^{(0)}}{p^j}+2n\,\frac{\sqrt2}{\sqrt2-1}.
--   $$
--
--   With $m^{(0)}=m$ and $j=t-1$ this bounds the length of the last string in the proof of Theorem 1 by $m/p^{t-1}+O(n)$.
--
--   Differences from the source:
--   - generalization: natural numbers n, m1, m^(j); p = (r/L)^{1/t}; 2np ≤ m1 ≤ 3np (Eq. (4)) → real n > 0, m₁, μ j ≥ 0; any real p ≥ √2; only 2np ≤ m₁; reason: the paper's quantities are such reals and satisfy these hypotheses (p ≥ √2 is shown on p. 10)
--   - encoding: m^(j), the length after j applications of the recurrence, m^(0) = m, while the recurrence is applied, with first step m^(j+1) ≤ 2n(m^(j)/m1 + 1) → μ : ℕ → ℝ with μ 0 the initial length, nonnegative for j ≤ J, with that first step as the hypothesis hrec for j < J; reason: J is the number of applications; lengths are nonnegative; the first step is the bound on m″ under Eq. (3), p. 10, which is what defines the sequence
--   - reading: "where the last equality follows since p ≥ √2" → the last relation is the inequality ≤; reason: the display has ≤; the word equality is a slip
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, §4, proof of Theorem 1 (unnumbered displays), p. 11

import Mathlib

namespace QRetrieval.Adaptive

/-- **The unrolled recursion: `m^(j) ≤ m/p^j + 2n Σ_{i<j} p^{−i} ≤ m/p^j + 2n √2/(√2 − 1)`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, §4, proof of Theorem 1 (unnumbered displays), p. 11: "Let `m^(j)` denote the
length of the string to be compressed after `j` applications of the recurrence, with
`m^(0) = m`. Whenever the recurrence is applied, we have (using Eq. (4))
`m^(j+1) ≤ 2n(m^(j)/m1 + 1) ≤ m^(j)/p + 2n`. … In general,
`m^(j) ≤ m/p^j + 2n Σ_{i=0}^{j−1} p^{−i} ≤ m/p^j + 2n(√2/(√2 − 1))`, where the last equality
follows since `p ≥ √2`."

Let `n > 0`, `p ≥ √2`, `m1 ≥ 2np` (Eq. (4), p. 10), and let `μ 0, …, μ J ≥ 0` (`μ j = m^(j)`,
`μ 0 = m`) satisfy `μ (j+1) ≤ 2n(μ j / m1 + 1)` for `j < J`. Then
1. `μ (j+1) ≤ μ j / p + 2n` for every `j < J`;
2. for every `j ≤ J`, `μ j ≤ μ 0 / p^j + 2n Σ_{i<j} p^{−i}` and
   `μ 0 / p^j + 2n Σ_{i<j} p^{−i} ≤ μ 0 / p^j + 2n · √2/(√2 − 1)`.

**Formalization Note.** `n`, `m1`, `p` and the lengths `μ j` are real numbers (the paper's are
natural numbers, `p = (r/L)^{1/t}`, and `m1 ≤ 3np` also holds; none of this is used). The page
calls the last inequality an "equality"; it is an inequality. -/
theorem recursion_length_bound (n m₁ p : ℝ) (μ : ℕ → ℝ) (J : ℕ) (hn : 0 < n)
    (hp : Real.sqrt 2 ≤ p) (hm₁ : 2 * n * p ≤ m₁) (hμ : ∀ j ≤ J, 0 ≤ μ j)
    (hrec : ∀ j < J, μ (j + 1) ≤ 2 * n * (μ j / m₁ + 1)) :
    (∀ j < J, μ (j + 1) ≤ μ j / p + 2 * n) ∧
    ∀ j ≤ J, μ j ≤ μ 0 / p ^ j + 2 * n * ∑ i ∈ Finset.range j, (p ^ i)⁻¹ ∧
      μ 0 / p ^ j + 2 * n * ∑ i ∈ Finset.range j, (p ^ i)⁻¹ ≤
        μ 0 / p ^ j + 2 * n * (Real.sqrt 2 / (Real.sqrt 2 - 1)) := by sorry

end QRetrieval.Adaptive
