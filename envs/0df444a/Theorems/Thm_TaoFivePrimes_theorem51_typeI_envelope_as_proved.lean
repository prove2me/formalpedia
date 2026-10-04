-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_envelope_as_proved
-- name    : TaoFivePrimes.theorem51_typeI_envelope_as_proved
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:13:50.991048+00:00
-- url     : https://prove2.me/theorems/4c58f243-1619-4ab4-9cdb-a82d6410841f
-- title:
--   Tao Theorem 5.1, Type I half, as its proof gives it
-- statement:
--   **The Type I half of Tao's Theorem 5.1, with the constants its proof gives.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$. Let $(c_d)$ be any complex coefficients with $|c_d|\le1$ on the positive odd $d\le UV$, and let $T_I(x,\alpha,U,V;c)=\sum_{d\le UV,\ d\text{ odd}}\bigl|\sum_{m\text{ odd}}(\log m+c_d\log d)\eta_0(\frac{dm}{x})e(\alpha dm)\bigr|$. Then
--
--   $$T_I(x,\alpha,U,V;c)\ \le\ \frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+1.78\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x).$$
--
--   These are the first two terms of Theorem 5.1 with the two changes the source's own Type I argument forces.
--
--   **The factor 2.** Each block $2jq+\frac q2<d\le2(j+1)q+\frac q2$ is bounded by the odd-restricted Vinogradov lemma. That block has length exactly $2q$, so the lemma's prefactor is $\lfloor\frac{2q}{2q}\rfloor+1=2$, giving $2(2A_j+\frac2\pi Cq\log4q)$ with $A_j=\frac12\frac{x}{2jq+q/2}\log x+C$ and $C=4(\log2)\log2x$. The source's display uses prefactor $1$. Carrying the correct one doubles both the harmonic term and the block bookkeeping, and $\frac{4\log2}{\pi}\le0.89$ becomes $\frac{8\log2}{\pi}\le1.78$.
--
--   **The additive 4.** The integral test $\sum_{0\le j\le\frac{UV}{2q}-\frac14}\frac{x}{2jq+\frac q2}\le\frac1{2q}\int_{q/2}^{UV+2q}\frac xy\,dy$ compares a decreasing summand with the integral over the preceding block, which covers $j\ge1$ but not $j=0$; the uncovered term is $\frac{x}{q/2}=\frac x{2q}\cdot4$. At $q=4$, $UV=40$ the sum is $0.7235x$ and the printed bound $0.3973x$.
--
--   Neither change costs anything downstream: Theorem 1.3 still follows with its printed constants, at $U=V=\frac1{10}x^{2/5}$.
--
--   **Formalization Note** The Type I sum, the divisor set and the smoothed cutoff are the platform definitions imported from `Def_TaoFivePrimes_Theorem51Sums`.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, estimation of the Type I sum, with both terms replaced by what the block decomposition and integral test yield

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeI_envelope_as_proved
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (c : ℕ → ℂ) (hc : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) :
    TaoFivePrimes.theorem51TypeI x alpha U V c ≤
      (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by sorry
