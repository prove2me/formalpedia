-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_small_q
-- name    : TaoFivePrimes.exp_sum_estimate_small_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T09:10:44.859345+00:00
-- url     : https://prove2.me/theorems/60299e07-cd93-4d63-9a0e-83f8431672e8
-- title:
--   Theorem 1.3, refinement (1.10) — small $q$
-- statement:
--   **Refinement (1.10) of Theorem 1.3, for small $q$.** Under the hypotheses of Theorem 1.3 — $x \geq 10^{20}$, $4\alpha = a/q + \beta$ with $100 \leq q \leq x/100$, $(a,q) = 1$, $|\beta| \leq 1/q^2$, and every prime factor of $q_0$ at most $\sqrt x$ — if additionally $q \leq x^{1/3}$, then
--
--   $$|S_{\eta_0,q_0}(x,\alpha)| \;\leq\; 0.5\,\frac{x}{q}(\log 2x)(\log 2x + 15) \;+\; 0.31\,\frac{x}{\sqrt q}\log q\,(\log q + 8.9).$$
--
--   The main estimate (1.9) is not sufficient across the whole range required by the circle-method argument of Section 8. For $q$ close to $1$ its first term $0.14\,x/\sqrt q$ is too weak, and this refinement replaces it by a term of size $x/q$, which is the correct order there. It is one of three refinements stated alongside (1.9); the companions cover $q$ near $x$.
--
--   **Formalization note.** The bound is written in the paper's form. $S_{\eta_0,q_0}$ is `smoothedExpSum eta0 q₀ x α`, and $x^{1/3}$ is `Real.rpow`.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Theorem 1.3, p. 5, refinement (1.10) (arXiv source label Sax-2).

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem exp_sum_estimate_small_q (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖smoothedExpSum eta0 q₀ x α‖ ≤
      0.5 * (x / q) * Real.log (2 * x) * (Real.log (2 * x) + 15)
        + 0.31 * (x / Real.sqrt q) * Real.log q * (Real.log q + 8.9) := by
  sorry

end TaoFivePrimes
