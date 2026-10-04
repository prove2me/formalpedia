-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_large_q
-- name    : TaoFivePrimes.exp_sum_estimate_large_q
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-07T09:10:45.281108+00:00
-- url     : https://prove2.me/theorems/b9bed795-df5b-4b21-9a35-52a227fb6852
-- title:
--   Theorem 1.3, refinement (1.11) — large $q$
-- statement:
--   **Refinement (1.11) of Theorem 1.3, for large $q$.** Under the hypotheses of Theorem 1.3 — $x \geq 10^{20}$, $4\alpha = a/q + \beta$ with $100 \leq q \leq x/100$, $(a,q) = 1$, $|\beta| \leq 1/q^2$, and every prime factor of $q_0$ at most $\sqrt x$ — if additionally $q \geq x^{2/3}$, then
--
--   $$|S_{\eta_0,q_0}(x,\alpha)| \;\leq\; 3.12\,\frac{x}{x/q}(\log 2x)(\log q + 8) \;+\; 1.19\,\frac{x}{\sqrt{x/q}}\log\frac{x}{q}\Bigl(\log\frac{x}{q} + 2.3\Bigr).$$
--
--   This is the counterpart of (1.10) at the other end of the range. When $q$ is close to $x$ the quantity $x/q$ is small, and the second term of (1.9), $0.64\,x/\sqrt{x/q}$, becomes too weak; the refinement is what makes Theorem 1.3 non-trivial across the whole window needed in Section 8.
--
--   **Formalization note.** The first coefficient is written as in the paper, $x/(x/q)$, rather than simplified to $q$, and the second as $x/\sqrt{x/q}$; the forms are kept verbatim so that the statement can be checked against the source line by line. $x^{2/3}$ is `Real.rpow`.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Theorem 1.3, p. 5, refinement (1.11) (arXiv source label Sax-3).

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem exp_sum_estimate_large_q (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hlarge : x ^ (2 / 3 : ℝ) ≤ (q : ℝ)) :
    ‖smoothedExpSum eta0 q₀ x α‖ ≤
      3.12 * (x / (x / q)) * Real.log (2 * x) * (Real.log q + 8)
        + 1.19 * (x / Real.sqrt (x / q)) * Real.log (x / q) * (Real.log (x / q) + 2.3) := by
  sorry

end TaoFivePrimes
