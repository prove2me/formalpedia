-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_envelope
-- name    : TaoFivePrimes.theorem51_typeI_envelope
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T16:27:04.405534+00:00
-- url     : https://prove2.me/theorems/71275065-0ae3-45b1-9749-c3f91c28b93e
-- title:
--   Tao Theorem 5.1, Type I half
-- statement:
--   **The Type I half of Tao's Theorem 5.1.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$. Let $(c_d)$ be any complex coefficients with $|c_d|\le1$ for every positive odd $d\le UV$, and let
--
--   $$T_I(x,\alpha,U,V;c)=\sum_{\substack{d\le UV\\ d\text{ odd}}}\Bigl|\sum_{m\text{ odd}}\bigl(\log m+c_d\log d\bigr)\eta_0\!\Bigl(\frac{dm}{x}\Bigr)e(\alpha dm)\Bigr|$$
--
--   be the Type I sum produced by the variant of Vaughan's identity. Then
--
--   $$T_I(x,\alpha,U,V;c)\ \le\ 0.5\,\frac xq(\log x)\log\Bigl(\frac{2UV}{q}+4\Bigr)+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x).$$
--
--   This is the first half of the source's Section 5: the two terms on the right are exactly the first two terms of Theorem 5.1. The argument is summation by parts in $m$ over blocks of length $2q$, the odd-restricted Vinogradov-type lemma on each block, and an integral test on the resulting harmonic sum over blocks.
--
--   **Note for anyone attacking this** Two of the source's intermediate displays in this passage do not come out as written. The integral test for the block sum drops an additive $4$: its $j=0$ term alone contributes $\frac{x}{2q}\cdot4$, so the display fails once $UV/q<\frac{e^4-4}2\approx25.3$ (at $q=1$, $UV=10$ the two sides are $2.8937x$ and $1.5890x$). And the per-block application of the odd-restricted Vinogradov lemma uses the factor $1$ where that lemma gives $\lfloor\frac{2q}{2q}\rfloor+1=2$, since the blocks have length exactly $2q$. The statement above is the source's, unmodified; a proof must recover that slack from the two terms rather than transcribe the chain.
--
--   **Formalization Note** The Type I sum, the divisor set and the smoothed cutoff are the platform definitions imported from `Def_TaoFivePrimes_Theorem51Sums`; the inner sum is over all odd integers $m=2n+1$, $n\in\mathbb Z$, made finite by the compact support of $\eta_0$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, proof of Theorem 5.1, the Type I estimate (the first two terms)

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeI_envelope
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (c : ℕ → ℂ) (hc : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) :
    TaoFivePrimes.theorem51TypeI x alpha U V c ≤
      0.5 * (x / q) * Real.log x * Real.log (2 * U * V / q + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by sorry
