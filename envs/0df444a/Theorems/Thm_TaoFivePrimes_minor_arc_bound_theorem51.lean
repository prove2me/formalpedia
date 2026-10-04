-- Prove2me | Theorems.Thm_TaoFivePrimes_minor_arc_bound_theorem51
-- name    : TaoFivePrimes.minor_arc_bound_theorem51
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T15:44:52.772642+00:00
-- url     : https://prove2.me/theorems/a6603036-1a7d-4f4c-a8fa-4952bea53143
-- title:
--   Tao Theorem 5.1: bound for minor arc sums
-- statement:
--   **Bound for minor arc sums.** Let $4\alpha=\frac aq+\beta$ for a natural number $q\ge4$ with $(a,q)=1$ and some $\beta=\mathcal O^*(1/q^2)$. Let $1<U,V<x$ and suppose
--   $$UV\le\frac x4,\qquad UV^2\ge x,\qquad U,V\ge40 .$$
--   Then
--
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\ \le\ & 0.5\,\frac xq(\log x)\log\Bigl(\frac{2UV}{q}+4\Bigr)+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x)\\
--   &+\Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}\\
--   &+\Bigl(0.55\frac{x}{\sqrt U}+0.78\frac{x}{\sqrt V}\Bigr)\log\frac xU .
--   \end{aligned}$$
--
--   Here $S_{\eta_0,2}(x,\alpha)=\sum_n\Lambda(n)\mathbf 1_{(n,2)=1}\eta_0(n/x)e(\alpha n)$ is the smoothed prime exponential sum sifted at the modulus $2$, with $\eta_0$ the source's logarithmic cutoff.
--
--   This is the central minor-arc estimate of the source: it is what Section 6 specializes, by choosing $U$ and $V$, to the exponential sum estimate quoted as Theorem 1.3, and through that it controls the minor arcs of the circle method. The proof splits $S_{\eta_0,2}$ by Vaughan's identity into a Type I sum, handled by summation by parts together with the Vinogradov-type lemma over blocks of length $2q$, and a Type II sum, handled by the dyadic representation of $\eta_0$ and the bilinear large sieve.
--
--   **Note for anyone attacking this** Three intermediate displays in the source's proof do not come out as written, all of them in the passage from the pointwise bounds to the two envelopes: the integral test for the Type I block sum drops an additive $4$ (its $j=0$ term alone is $\frac{x}{2q}\cdot4$, so the display fails once $UV/q<\frac{e^4-4}2\approx25.3$; at $q=1$, $UV=10$ the sides are $2.8937x$ and $1.5890x$); the per-block application of the odd-restricted Vinogradov lemma uses the factor $1$ where that lemma gives $\lfloor\frac{2q}{2q}\rfloor+1=2$; and the third coefficient of the Type II square-root expansion is $1$ rather than $\frac1{\sqrt2}$, since $\sqrt{2q}\sqrt{\frac{x}{2Wq}}\sqrt x=x\sqrt{\frac{2q}{2Wq}}=\frac x{\sqrt W}$. The statement above is the source's, unmodified; a proof will have to recover the slack from the remaining terms rather than transcribe the chain.
--
--   **Formalization Note** The alternative form of the first term available when $a=\pm1$ and $UV<q-1$ is omitted, since the derivation of Theorem 1.3 does not use it. The smoothed sum is the platform definition, an unconditional sum over the natural numbers made finite by the compact support of $\eta_0$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, Theorem 5.1 (Bound for minor arc sums), the estimate (term-1) together with the two following displays; the alternative term (term-1-alt) valid for a = +-1 and UV < q-1 is omitted

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount

open Finset

theorem TaoFivePrimes.minor_arc_bound_theorem51
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU1 : 1 < U) (hV1 : 1 < V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
      0.5 * (x / q) * Real.log x * Real.log (2 * U * V / q + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * x / Real.sqrt U + 0.78 * x / Real.sqrt V) * Real.log (x / U) := by sorry
