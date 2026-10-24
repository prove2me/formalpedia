-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_4_2
-- name    : RecMarkovGraph.IndepLB.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:30.36463+00:00
-- url     : https://prove2.me/theorems/2887f934-6d3d-4052-a8a6-d874b3427f25
-- title:
--   Lemma 4.2, p. 10 (corrected: ℓ_n(a x_1) for ℓ_n(x_1), and x_n ≤ 1/(4a) non-strict) — the recursion decreases and (1/a)ℓ_n(ax_1) ≤ x_n < 1/(a(n − 1 + 1/x_1))
-- statement:
--   Let $a\in(0,1]$, $x_1\in(0,1)$ and $x_{n+1}=f_a(x_n)=x_n(1-ax_n)$. Then the sequence is strictly decreasing, $x_{n+1}<x_n$ for all $n\ge1$, and for every $n\ge2$
--   $$\frac1a\,\ell_n(a x_1)\ \le\ x_n,\qquad x_n\le\frac1{4a},\qquad x_n<\frac1a\cdot\frac{1}{n-1+1/x_1},$$
--   where $\ell_n$ is the function of display (4).
--
--   The terms of the recursion are thus of order $1/n$; through Lemma 3.1 these bounds become the bounds of Lemma 6.1 on the edge probabilities of $G^r_{n,p}$.
--
--   Differences from the source:
--   - correction: lower bound (1/a) ℓ_n(x_1) ⩽ x_n → ell n (a * x₁) / a ≤ x_n, i.e. (1/a) ℓ_n(a x_1); reason: the printed bound is false for a < 1: a = 0.2, x_1 = 0.01, n = 2 gives x_2 = 0.00998 < (1/a) ℓ_2(x_1) = 0.02475; the proof reduces to a = 1 through y_n = a x_n, which yields ℓ_n(a x_1), the form Lemma 6.1 uses (ℓ_j(γp)/γ)
--   - correction: x_n < (1/a) min{1/4, ·}, strict in the 1/4 term → x_n ≤ 1/(4a) (non-strict) together with the strict x_n < (1/a)/(n − 1 + 1/x_1); reason: a = 1, x_1 = 1/2, n = 2 gives x_2 = 1/4 = 1/(4a)
--   - reading: "generates a decreasing sequence" → recSeq a x₁ (k+1) < recSeq a x₁ k for all k; reason: strictly decreasing, the stronger reading; true since x_n > 0
--   - encoding: x_n, n ≥ 1; x < min{A, B} → recSeq a x₁ (n − 1); the minimum split into the two bounds; reason: 0-based sequence index; x < min{A, B} is x < A ∧ x < B
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 10, Lemma 4.2 and (4) (proof in §9, pp. 22–23)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

theorem lemma_4_2 (a x₁ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx₁ : 0 < x₁) (hx₁1 : x₁ < 1) :
    (∀ k : ℕ, recSeq a x₁ (k + 1) < recSeq a x₁ k) ∧
    ∀ n : ℕ, 2 ≤ n →
      ell n (a * x₁) / a ≤ recSeq a x₁ (n - 1) ∧
      recSeq a x₁ (n - 1) ≤ 1 / (4 * a) ∧
      recSeq a x₁ (n - 1) < 1 / a * (1 / ((n : ℝ) - 1 + 1 / x₁)) := by sorry

end RecMarkovGraph.IndepLB
