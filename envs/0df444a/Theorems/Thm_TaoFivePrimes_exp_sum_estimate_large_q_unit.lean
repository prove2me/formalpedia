-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_large_q_unit
-- name    : TaoFivePrimes.exp_sum_estimate_large_q_unit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-07T09:10:44.434808+00:00
-- url     : https://prove2.me/theorems/aff0354f-39ac-428b-b93a-57fc43055689
-- title:
--   Theorem 1.3, refinement (1.12) — large $q$ with $a = \pm 1$
-- statement:
--   **Refinement (1.12) of Theorem 1.3, for large $q$ with unit numerator.** Under the hypotheses of Theorem 1.3 — $x \geq 10^{20}$, $4\alpha = a/q + \beta$ with $100 \leq q \leq x/100$, $(a,q) = 1$, $|\beta| \leq 1/q^2$, and every prime factor of $q_0$ at most $\sqrt x$ — if additionally $q \geq x^{2/3}$ and $a = \pm 1$, then
--
--   $$|S_{\eta_0,q_0}(x,\alpha)| \;\leq\; 9.73\,\frac{x}{(x/q)^2}\log^2 x \;+\; 1.2\,\frac{x}{\sqrt{x/q}}\log\frac{x}{q}\Bigl(\log\frac{x}{q} + 2.4\Bigr).$$
--
--   This is the sharpest of the three refinements, available in the special case where the rational approximation to $4\alpha$ has numerator $\pm 1$, which is exactly the situation for frequencies very close to a rational with small denominator. It improves the first term of (1.11) from order $x/(x/q)$ to order $x/(x/q)^2$, at the cost of the extra hypothesis on $a$.
--
--   **Formalization note.** The coefficients are kept in the paper's unsimplified form, $x/(x/q)^2$ and $x/\sqrt{x/q}$, so the statement can be checked against the source directly. The hypothesis $a = \pm 1$ is the disjunction `a = 1 ∨ a = -1` on the integer numerator, and $x^{2/3}$ is `Real.rpow`.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Theorem 1.3, p. 5, refinement (1.12) (arXiv source label lab).

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem exp_sum_estimate_large_q_unit (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hlarge : x ^ (2 / 3 : ℝ) ≤ (q : ℝ)) (ha : a = 1 ∨ a = -1) :
    ‖smoothedExpSum eta0 q₀ x α‖ ≤
      9.73 * (x / (x / q) ^ 2) * Real.log x ^ 2
        + 1.2 * (x / Real.sqrt (x / q)) * Real.log (x / q) * (Real.log (x / q) + 2.4) := by
  sorry

end TaoFivePrimes
