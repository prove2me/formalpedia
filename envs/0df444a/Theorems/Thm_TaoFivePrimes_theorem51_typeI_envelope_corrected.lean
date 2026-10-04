-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_envelope_corrected
-- name    : TaoFivePrimes.theorem51_typeI_envelope_corrected
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T16:57:06.807751+00:00
-- url     : https://prove2.me/theorems/38d77bc8-9ac9-495c-b946-ae2b106d2394
-- title:
--   Tao Theorem 5.1, Type I half, with the constant its proof supports
-- statement:
--   **The Type I half of Tao's Theorem 5.1, with the constant its proof supports.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$. Let $(c_d)$ be any complex coefficients with $|c_d|\le1$ for every positive odd $d\le UV$, and let
--
--   $$T_I(x,\alpha,U,V;c)=\sum_{\substack{d\le UV\\ d\text{ odd}}}\Bigl|\sum_{m\text{ odd}}\bigl(\log m+c_d\log d\bigr)\eta_0\!\Bigl(\frac{dm}{x}\Bigr)e(\alpha dm)\Bigr|$$
--
--   be the Type I sum produced by the variant of Vaughan's identity. Then
--
--   $$T_I(x,\alpha,U,V;c)\ \le\ 0.5\,\frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x).$$
--
--   This is the first half of the source's Section 5, and the two terms on the right are the first two terms of Theorem 5.1 with the first weakened by an additive $4$ inside the bracket.
--
--   **Why the additive 4** After summation by parts over blocks of length $2q$ and the odd-restricted Vinogradov lemma, the source is left with $\sum_{0\le j\le\frac{UV}{2q}-\frac14}\frac{x}{2jq+\frac q2}$ and bounds it by $\frac1{2q}\int_{q/2}^{UV+2q}\frac xy\,dy=\frac x{2q}\log(\frac{2UV}q+4)$. Comparing a decreasing summand with the integral over the preceding block of length $2q$ covers the terms $j\ge1$ but not $j=0$, whose term is $\frac{2x}{q}=\frac{x}{2q}\cdot4$. At $q=4$, $UV=40$ the sum is $0.7235x$ and the printed bound $0.3973x$. The statement above restores the missing term; asymptotically in $UV/q$ it costs nothing, and Section 6 absorbs it with room to spare.
--
--   **Formalization Note** The Type I sum, the divisor set and the smoothed cutoff are the platform definitions imported from `Def_TaoFivePrimes_Theorem51Sums`; the inner sum runs over all odd integers $m=2n+1$, $n\in\mathbb Z$, and is finite because $\eta_0$ has compact support.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, proof of Theorem 5.1, the Type I estimate, with the first term weakened to match the integral test of its own proof

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeI_envelope_corrected
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (c : ℕ → ℂ) (hc : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) :
    TaoFivePrimes.theorem51TypeI x alpha U V c ≤
      0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by sorry
