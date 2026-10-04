-- Prove2me | Theorems.Thm_TaoFivePrimes_minor_arc_bound_theorem51_corrected
-- name    : TaoFivePrimes.minor_arc_bound_theorem51_corrected
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T16:45:25.777347+00:00
-- url     : https://prove2.me/theorems/27b24096-d7a7-41d4-a1b8-6df209b569ae
-- title:
--   Tao Theorem 5.1 with the constants its proof supports
-- statement:
--   **Bound for minor arc sums, with the constants the source's own argument supports.** Let $4\alpha=\frac aq+\beta$ for a natural number $q\ge4$ with $(a,q)=1$ and $|\beta|\le q^{-2}$. Let $1<U,V<x$ with
--   $$UV\le\frac x4,\qquad UV^2\ge x,\qquad U,V\ge40 .$$
--   Then
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\ \le\ & 0.5\,\frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x)\\
--   &+\Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+1.1\frac{x}{\sqrt V}\Bigr)\log\frac xU .
--   \end{aligned}$$
--
--   Here $S_{\eta_0,2}(x,\alpha)=\sum_n\Lambda(n)\mathbf 1_{(n,2)=1}\eta_0(n/x)e(\alpha n)$ is the smoothed prime exponential sum sifted at the modulus $2$.
--
--   This is the central minor-arc estimate of the source, stated with two constants weakened to what the source's own chain of estimates actually yields. It is still strong enough for everything the source does with it: Section 6 specialises it at $U=\frac14x^{2/5}$, $V=\frac12x^{2/5}$ to the exponential sum estimate quoted as Theorem 1.3, and the margin there is ample.
--
--   **Where the two changes come from** The source states the first term without the additive $4$ and the last with $0.78$ in place of $1.1$. Neither is supported by its own argument.
--
--   *First term.* The integral test used for the block sum is
--   $$\sum_{0\le j\le\frac{UV}{2q}-\frac14}\frac{x}{2jq+\frac q2}\ \le\ \frac1{2q}\int_{q/2}^{UV+2q}\frac xy\,dy=\frac x{2q}\log\Bigl(\frac{2UV}{q}+4\Bigr),$$
--   but the comparison of a decreasing summand with the integral over the preceding block does not cover $j=0$, whose term is $\frac{2x}{q}=\frac{x}{2q}\cdot4$. At $q=4$, $UV=40$ the left side is $0.7235x$ and the right side $0.3973x$. Restoring the missing term gives the $+4$ above; asymptotically in $UV/q$ it costs nothing.
--
--   *Last term.* In the square-root expansion of the Type II envelope the third coefficient is
--   $$\sqrt{2q}\cdot\sqrt{\frac{x}{2Wq}}\cdot\sqrt x=x\sqrt{\frac{2q}{2Wq}}=\frac{x}{\sqrt W},$$
--   that is $1$ and not $\frac1{\sqrt2}$. Carrying the corrected coefficient through $4\int_V^{x/U}\frac{dW}{W}$ turns the source's $\frac{1.1}{\sqrt2}\le0.78$ into $1.1$.
--
--   **Formalization Note** The alternative form of the first term available when $a=\pm1$ and $UV<q-1$ is omitted, since the derivation of Theorem 1.3 does not use it. The smoothed sum is the platform definition, an unconditional sum over the natural numbers made finite by the compact support of $\eta_0$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, Theorem 5.1, with the first and fourth terms weakened to match the integral test and the square-root expansion of its own proof

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount

open Finset

theorem TaoFivePrimes.minor_arc_bound_theorem51_corrected
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU1 : 1 < U) (hV1 : 1 < V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
      0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by sorry
