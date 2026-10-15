-- Prove2me | Theorems.Thm_PosetSecretary_ProxyLabel_label_max_prob
-- name    : PosetSecretary.ProxyLabel.label_max_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:22.967738+00:00
-- url     : https://prove2.me/theorems/cb65ee6e-df99-4324-ab4c-7cc1e724ec3d
-- title:
--   Proof of Proposition 5.2, p. 16, first display — P(a_j is maximum in its label class) = (1 − 1/k)^{j−1} ≥ (1 − 1/k)^{k−1} ≥ 1/e
-- statement:
--   Let $C$ be a finite set with pairwise distinct scores $w : C \to \mathbb R$, let $k \ge 1$, and let $a_j \in C$ be the $j$-th best element, $1 \le j \le k$: exactly $j - 1$ elements $a_1, \dots, a_{j-1}$ have a larger score than $a_j$. Assign every element a label in $\{1, \dots, k\}$ uniformly and independently. Then the probability that $a_j$ has the largest score in its label class, that is, that none of $a_1, \dots, a_{j-1}$ shares its label, is
--
--   $$\mathbb P\big(w(a_j) = \max\{w(a) : \ell(a) = \ell(a_j)\}\big) = \Big(1 - \frac1k\Big)^{j-1} \ \ge\ \Big(1 - \frac1k\Big)^{k-1} \ \ge\ \frac1e .$$
--
--   This is the first step of the proof of Proposition 5.2: each of the top $k$ elements is, with probability at least $1/e$, the maximum of its label class, which is the situation in which ProxyLabel can select it.
--
--   **Formalization Note** The probability is the fraction of the $k^N$ labellings `α → Fin k` under which no element of larger score has the label of $a_j$. Exponents are natural numbers, so at $k = 1$ the bound reads $0^0 = 1$, the paper's convention. Only distinctness of the scores is assumed; the partial order plays no role here.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.2, p. 16, first display

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PosetSecretary.ProxyLabel

/-- Proof of Proposition 5.2, p. 16, first display (Salem & Gupta, SSRN 3444283): if exactly
`j - 1` elements score above `a`, with `1 ≤ j ≤ k`, then under a uniformly random labelling
the probability that `a` is maximum in its labeled group is `(1 - 1/k)^(j-1)`, which is at least
`(1 - 1/k)^(k-1) ≥ 1/e`. -/
theorem label_max_prob {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ)
    (hinj : Function.Injective w) (k : ℕ) (hk : 1 ≤ k) (a : α) (j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (hrank : (Finset.univ.filter (fun b => w a < w b)).card = j - 1) :
    labelMaxProb w k a = (1 - 1 / (k : ℝ)) ^ (j - 1) ∧
      (1 - 1 / (k : ℝ)) ^ (k - 1) ≤ (1 - 1 / (k : ℝ)) ^ (j - 1) ∧
      1 / Real.exp 1 ≤ (1 - 1 / (k : ℝ)) ^ (k - 1) := by sorry

end PosetSecretary.ProxyLabel
