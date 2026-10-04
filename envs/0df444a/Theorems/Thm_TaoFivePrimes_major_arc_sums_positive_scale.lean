-- Prove2me | Theorems.Thm_TaoFivePrimes_major_arc_sums_positive_scale
-- name    : TaoFivePrimes.major_arc_sums_positive_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-09-29T05:18:20.569093+00:00
-- url     : https://prove2.me/theorems/34fa3091-8a46-4ae4-b907-596a0ba9e6db
-- title:
--   Tao, Proposition 7.2 — major arc sums (positive scale, zeros with multiplicity)
-- statement:
--   **Proposition 7.2 (Major arc sums).** Let $T_0 = 3.29 \times 10^9$ be the height of Theorem 1.5. Let $\eta:\mathbb R\to\mathbb R$ be a smooth non-negative function supported on $[c,c']$ with $c>0$, and let $x,\alpha$ be reals with $cx \geq 10^3$ and
--
--   $$|\alpha| \;\leq\; \frac{T_0}{4\pi c' x}.$$
--
--   Then
--
--   $$\Bigl|S_{\eta,1}(x,\alpha) - x\int_{\mathbb R} \eta(y)\,e(\alpha x y)\,dy\Bigr| \;\leq\; A\,\frac{\log T_0}{3T_0}\,x \;+\; 2.01\,c^{-1/2}x^{1/2}N(T_0)\,\|\eta\|_{L^1(\mathbb R)},$$
--
--   where
--
--   $$A := 60\|\eta\|_{L^1} + 32c'\|\eta'\|_{L^1} + 4(c')^2\|\eta''\|_{L^1},$$
--
--   and $N(T_0)$ is the number of zeroes of $\zeta$, **counted with multiplicity**, in the strip $\{0 \leq \Re(s) \leq 1,\ 0 \leq \Im(s) \leq T_0\}$. Here $S_{\eta,1}(x,\alpha)=\sum_{n}\Lambda(n)\,\eta(n/x)\,e(\alpha n)$ and $e(\theta)=e^{2\pi i\theta}$.
--
--   **Role.** This is the estimate that controls the exponential sum on the major arc $\alpha = O(T_0/x)$ by comparing it with the archimedean integral $x\int\eta(y)e(\alpha xy)\,dy$. The error is governed by the zeroes of $\zeta$ below height $T_0$, which is where the numerical verification of Theorem 1.5 enters. It feeds the strongly major arc estimate of Section 8.
--
--   **Relation to `TaoFivePrimes.major_arc_sums`.** That earlier node transcribed the proposition without the positivity of $c$, which the source takes for granted since $\eta$ lives on $\mathbb R^+$ and $[c,c']$ is a support interval. It was disproved by taking $c<0$, $x<0$, $c'=0$, where Lean's conventions $\sqrt{c}=0$ and $a/0=0$ make the right-hand side negative. This node restores exactly that hypothesis; $x>0$ then follows from $cx\ge10^3$. It also counts zeroes with multiplicity, as the source's proof requires: the explicit formula sums over zeroes with multiplicity, and each zero with $|\Im\rho|\le T_0$ contributes at most $c^{-1/2}x^{1/2}\|\eta\|_{L^1}$. The earlier node used the number of distinct zeroes, which is only equivalent given simplicity of the zeroes, an input the source does not use.
--
--   **Formalization notes.** $N(T_0)$ is the finite sum of `analyticOrderNatAt riemannZeta s` over the zeroes $s$ in the closed strip. The strip contains finitely many zeroes, and at each of them $\zeta$ is analytic (they avoid the pole $s=1$) and not locally zero, so this is the order of vanishing, i.e. the multiplicity. The constant $A$ is inlined; the $L^1$ norms are the integrals $\int|\eta|$, $\int|\eta'|$, $\int|\eta''|$ with iterated `deriv`. The height $T_0$ is the literal $3.29\times10^9$, so a proof is expected to import `riemann_verified`. Support on $[c,c']$ is expressed as $\eta(y)\ne0\to y\in[c,c']$, and $c^{-1/2}$, $x^{1/2}$ as `1 / Real.sqrt c`, `Real.sqrt x`. No hypothesis $c\le c'$ is needed: if $c>c'$ then $\eta\equiv0$ and both sides vanish.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 7 (Major arc estimate), Proposition 7.2 (arXiv source label rh), displays (7.2)-(7.4). Restores the implicit positivity c > 0 omitted by the disproved TaoFivePrimes.major_arc_sums, and counts N(T0) with multiplicity as the proof's explicit-formula sum over zeroes requires.

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem major_arc_sums_positive_scale (η : ℝ → ℝ) (c c' x α : ℝ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hnonneg : ∀ y, 0 ≤ η y)
    (hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc c c')
    (hc : 0 < c)
    (hcx : (10 : ℝ) ^ 3 ≤ c * x)
    (hα : |α| ≤ 3.29 * 10 ^ 9 / (4 * Real.pi * c' * x)) :
    ‖smoothedExpSum η 1 x α - (x : ℂ) * ∫ y : ℝ, (η y : ℂ) * expCircle (α * x * y)‖ ≤
      (60 * (∫ y, |η y|) + 32 * c' * (∫ y, |deriv η y|)
          + 4 * c' ^ 2 * (∫ y, |deriv (deriv η) y|))
        * (Real.log (3.29 * 10 ^ 9) / (3 * (3.29 * 10 ^ 9))) * x
      + 2.01 / Real.sqrt c * Real.sqrt x
          * (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
                riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ))
          * (∫ y, |η y|) := by
  sorry

end TaoFivePrimes
