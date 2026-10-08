-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_poisson_tail_bound
-- name    : ResolvingNRM.IRT.poisson_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:20:55.202423+00:00
-- url     : https://prove2.me/theorems/52e75797-1cee-4d1f-a539-5f974578b87f
-- title:
--   Lemma 4, p. 37 — Poisson tail bound $P(|X-\lambda|\ge x) \le 2e^{-x^2/(3\lambda)}$ for $0 < x \le \lambda$
-- statement:
--   Let $X$ be a Poisson random variable with parameter $\mu > 0$. For every $x$ with $0 < x \le \mu$,
--   $$\mathbb P\big(|X - \mu| \ge x\big) \le 2\exp\Big(-\frac{x^2}{3\mu}\Big).$$
--
--   This is the concentration inequality the paper uses (in Lemma 6) to show that the acceptance counts of the first epoch of IRT stay close to their means with overwhelming probability.
--
--   **Formalization Note** The hypothesis $x \le \mu$ is added. The paper states the bound for every $x > 0$, which is false: for $\mu = 1$, $x = 5$ one has $\mathbb P(|X-1| \ge 5) = \mathbb P(X \ge 6) \approx 5.94\cdot 10^{-4} > 2e^{-25/3} \approx 4.81\cdot 10^{-4}$. Every use of the lemma in the paper is in the range $0 < x \le \mu$. The probability is written as the sum of the Poisson masses $e^{-\mu}\mu^k/k!$ over the $k \in \mathbb N$ with $|k - \mu| \ge x$.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Lemma 4 (Poisson Tail Bound, Pollard (2015)), p. 37

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem poisson_tail_bound (μ x : ℝ) (hμ : 0 < μ) (hx : 0 < x) (hxμ : x ≤ μ) :
    ∑' k : ℕ, (if x ≤ |(k : ℝ) - μ| then poissonPMF μ k else 0) ≤
      2 * Real.exp (-(x ^ 2) / (3 * μ)) := by sorry

end ResolvingNRM.IRT
