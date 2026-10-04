-- Prove2me | Theorems.Thm_TaoFivePrimes_minor_arc_bound_theorem51_as_proved
-- name    : TaoFivePrimes.minor_arc_bound_theorem51_as_proved
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:03:59.122627+00:00
-- url     : https://prove2.me/theorems/813a0c86-205c-4486-923b-baa84beae281
-- title:
--   Tao Theorem 5.1 as its proof gives it
-- statement:
--   **Bound for minor arc sums, with the constants its own proof yields.** Let $4\alpha=\frac aq+\beta$ for a natural number $q\ge4$ with $(a,q)=1$ and $|\beta|\le q^{-2}$. Let $1<U,V<x$ with $UV\le\frac x4$, $UV^2\ge x$ and $U,V\ge40$. Then
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\ \le\ & \frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+1.78\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x)\\
--   &+\Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+1.1\frac{x}{\sqrt V}\Bigr)\log\frac xU .
--   \end{aligned}$$
--
--   This is the source's Theorem 5.1 with each of its four terms replaced by what its own chain of estimates delivers. The source prints $0.5$, $0.89$ and $0.78$ where this statement has $1$ (with an extra additive $4$), $1.78$ and $1.1$. It is still strong enough for everything the source does with it: the exponential sum estimate of Theorem 1.3 follows from this form with its printed constants, at $U=V=\frac1{10}x^{2/5}$ rather than the source's $U=\frac14x^{2/5}$, $V=\frac12x^{2/5}$.
--
--   **Where the three changes come from**
--
--   *The factor $2$ in the first two terms.* The Type I argument bounds each block $2jq+\frac q2<d\le2(j+1)q+\frac q2$ by Corollary 3.5. That block has length exactly $2q$, so the corollary's prefactor is $\lfloor\frac{2q}{2q}\rfloor+1=2$, giving $2\bigl(2A_j+\frac2\pi Cq\log4q\bigr)$ with $A_j=\frac12\frac{x}{2jq+q/2}\log x+C$ and $C=4(\log2)\log2x$. The source's display uses $2A_j+\frac2\pi Cq\log 4q$, that is prefactor $1$. Carrying the correct prefactor doubles both the harmonic term and the block bookkeeping, and $\frac{4\log2}\pi\le0.89$ becomes $\frac{8\log2}\pi\le1.78$.
--
--   *The additive $4$.* The integral test $\sum_{0\le j\le\frac{UV}{2q}-\frac14}\frac{x}{2jq+\frac q2}\le\frac1{2q}\int_{q/2}^{UV+2q}\frac xy\,dy$ compares a decreasing summand with the integral over the preceding block of length $2q$, which covers $j\ge1$ but not $j=0$; the uncovered term is $\frac{x}{q/2}=\frac{x}{2q}\cdot4$. At $q=4$, $UV=40$ the sum is $0.7235x$ and the printed bound $0.3973x$.
--
--   *The last constant.* In the square-root expansion of the Type II envelope the cross term is $\sqrt{2q}\cdot\sqrt{\frac{x}{2Wq}}\cdot\sqrt x=x\sqrt{\frac{2q}{2Wq}}=\frac{x}{\sqrt W}$, coefficient $1$ and not $\frac1{\sqrt2}$; integrating against $\frac{4dW}{W}$ turns $\frac{1.1}{\sqrt2}\le0.78$ into $1.1$.
--
--   **Formalization Note** The alternative form of the first term available when $a=\pm1$ and $UV<q-1$ is omitted, since the derivation of Theorem 1.3 does not use it. The smoothed sum is the platform definition.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, Theorem 5.1, with all four terms replaced by what the proof of that theorem yields

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount

open Finset

theorem TaoFivePrimes.minor_arc_bound_theorem51_as_proved
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU1 : 1 < U) (hV1 : 1 < V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
      (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by sorry
