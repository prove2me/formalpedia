-- Prove2me | Theorems.Thm_TaoFivePrimes_major_arc_sums
-- name    : TaoFivePrimes.major_arc_sums
-- status  : Disproved
-- author  : @marwahaha
-- created : 2026-09-07T09:19:51.438949+00:00
-- url     : https://prove2.me/theorems/b03e9980-44fa-4b79-a2d3-45cdebc076d8
-- title:
--   Proposition 7.2 — major arc sums
-- statement:
--   **Proposition 7.2 (Major arc sums).** Let $T_0 = 3.29 \times 10^9$ be the height of Theorem 1.5. Let $\eta$ be a smooth non-negative function supported on $[c,c']$, and let $x,\alpha$ be reals with $cx \geq 10^3$ and
--
--   $$|\alpha| \;\leq\; \frac{T_0}{4\pi c' x}.$$
--
--   Then
--
--   $$\Bigl|S_{\eta,1}(x,\alpha) - x\int_{\mathbb R} \eta(y)\,e(\alpha x y)\,dy\Bigr| \;\leq\; A\,\frac{\log T_0}{3T_0}\,x \;+\; 2.01\,c^{-1/2}x^{1/2}N(T_0)\|\eta\|_{L^1(\mathbb R)},$$
--
--   where
--
--   $$A := 60\|\eta\|_{L^1} + 32c'\|\eta'\|_{L^1} + 4(c')^2\|\eta''\|_{L^1}$$
--
--   and $N(T_0)$ is the number of zeroes of $\zeta$ in the strip $\{0 \leq \Re(s) \leq 1,\ 0 \leq \Im(s) \leq T_0\}$.
--
--   **Role.** This is the estimate that controls the exponential sum in the major arc regime $\alpha = O(T_0/x)$, by comparing it against the archimedean integral $x\int\eta(y)e(\alpha x y)\,dy$; the error is governed by the zeroes of $\zeta$ below height $T_0$, which is where the numerical verification of Theorem 1.5 enters. It is the input to the strongly major arc estimate of Section 8, rather than that estimate itself. For the chosen $T_0$, the paper notes $N(T_0)$ may be bounded by $10^{10}$ — indeed $T_0$ was chosen from the verification that the first $10^{10}$ zeroes lie on the critical line.
--
--   The paper remarks that the hypothesis on $|\alpha|$ permits $|\alpha| > 1$, which may look odd; in that regime the bound is simply weaker than the trivial estimate, so nothing is lost.
--
--   **Formalization notes.** The modulus is $q_0 = 1$, which imposes no coprimality restriction, matching $S_{\eta,1}$ in the source. The constant $A$ is inlined rather than named, and the $L^1$ norms are the integrals $\int|\eta|$, $\int|\eta'|$, $\int|\eta''|$ with derivatives taken as iterated `deriv`. $N(T_0)$ is the `Set.ncard` of the zero set of `riemannZeta` in the closed strip. The height $T_0$ is written as the literal $3.29\times10^9$ rather than carried as a variable, since Proposition 7.2 is stated for the specific height of Theorem 1.5; a proof is therefore expected to import `riemann_verified`. Support on $[c,c']$ is expressed as $\eta(y) \neq 0 \to y \in [c,c']$, and $c^{-1/2}$, $x^{1/2}$ as `1 / Real.sqrt c` and `Real.sqrt x`.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 7 (Major arc estimate), Proposition 7.2 (arXiv source label rh), displays (7.2)-(7.4).

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem major_arc_sums (η : ℝ → ℝ) (c c' x α : ℝ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hnonneg : ∀ y, 0 ≤ η y)
    (hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc c c')
    (hcx : (10 : ℝ) ^ 3 ≤ c * x)
    (hα : |α| ≤ 3.29 * 10 ^ 9 / (4 * Real.pi * c' * x)) :
    ‖smoothedExpSum η 1 x α - (x : ℂ) * ∫ y : ℝ, (η y : ℂ) * expCircle (α * x * y)‖ ≤
      (60 * (∫ y, |η y|) + 32 * c' * (∫ y, |deriv η y|)
          + 4 * c' ^ 2 * (∫ y, |deriv (deriv η) y|))
        * (Real.log (3.29 * 10 ^ 9) / (3 * (3.29 * 10 ^ 9))) * x
      + 2.01 / Real.sqrt c * Real.sqrt x
          * ({s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
                riemannZeta s = 0}.ncard : ℝ)
          * (∫ y, |η y|) := by
  sorry

end TaoFivePrimes
