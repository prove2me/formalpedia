-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_envelope_corrected
-- name    : TaoFivePrimes.theorem51_typeII_envelope_corrected
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T16:57:10.597157+00:00
-- url     : https://prove2.me/theorems/25891e2a-df76-428c-8bd8-dad0872dd4b3
-- title:
--   Tao Theorem 5.1, Type II half, with the constant its proof supports
-- statement:
--   **The Type II half of Tao's Theorem 5.1, with the constant its proof supports.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$. Let
--
--   $$T_{II}(x,\alpha,U,V)=\Bigl|\sum_{\substack{d>U,\ w>V\\ d,w\text{ odd}}}\mu(d)\Bigl(\sum_{\substack{b\mid w\\ b>V}}\Lambda(b)-\tfrac12\log w\Bigr)\eta_0\!\Bigl(\frac{dw}{x}\Bigr)e(\alpha dw)\Bigr|$$
--
--   be the bilinear Type II sum produced by the variant of Vaughan's identity, with the centred divisor coefficient of the source's equation (4.19). Then
--
--   $$T_{II}(x,\alpha,U,V)\ \le\ \Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+1.1\frac{x}{\sqrt V}\Bigr)\log\frac xU .$$
--
--   This is the second half of the source's Section 5, and the two terms on the right are the last two terms of Theorem 5.1 with the last weakened from $0.78$ to $1.1$.
--
--   **Why 1.1 and not 0.78** Writing $\eta_0$ through its dyadic integral representation gives $T_{II}\le4\int_0^\infty F(W)\frac{dW}{W}$, and the subdivision form of the odd bilinear large sieve bounds $F(W)$ by $\frac{1.1}8(\frac W4+2q)^{1/2}(\frac{x}{2Wq}+1)^{1/2}x^{1/2}\log W$. Expanding both square roots by $(a+b)^{1/2}\le a^{1/2}+b^{1/2}$, the cross term $\sqrt{2q}\cdot\sqrt{\frac{x}{2Wq}}\cdot\sqrt x$ equals $x\sqrt{\frac{2q}{2Wq}}=\frac{x}{\sqrt W}$, so its coefficient is $1$ and not $\frac1{\sqrt2}$ as printed. Integrating $\frac x{\sqrt W}$ against $\frac{4\,dW}{W}$ over $V\le W\le\frac xU$, with $\log W$ bounded by $\log\frac xU$, contributes $4\cdot\frac{1.1}8\cdot2\frac{x}{\sqrt V}\log\frac xU=1.1\frac{x}{\sqrt V}\log\frac xU$ in place of the printed $\frac{1.1}{\sqrt2}\le0.78$. Section 6 absorbs the difference.
--
--   **Formalization Note** The Type II sum and the centred coefficient are the platform definitions imported from `Def_TaoFivePrimes_Theorem51Sums`; the double sum runs over all natural numbers and is finite because $\eta_0$ has compact support.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, proof of Theorem 5.1, the Type II estimate, with the last term weakened to match the square-root expansion of its own proof

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeII_envelope_corrected
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by sorry
