-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_envelope
-- name    : TaoFivePrimes.theorem51_typeII_envelope
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T16:27:07.769274+00:00
-- url     : https://prove2.me/theorems/263c6196-00ae-4029-add5-f0bdeec5c40a
-- title:
--   Tao Theorem 5.1, Type II half
-- statement:
--   **The Type II half of Tao's Theorem 5.1.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$. Let
--
--   $$T_{II}(x,\alpha,U,V)=\Bigl|\sum_{\substack{d>U,\ w>V\\ d,w\text{ odd}}}\mu(d)\Bigl(\sum_{\substack{b\mid w\\ b>V}}\Lambda(b)-\tfrac12\log w\Bigr)\eta_0\!\Bigl(\frac{dw}{x}\Bigr)e(\alpha dw)\Bigr|$$
--
--   be the bilinear Type II sum produced by the variant of Vaughan's identity, with the centred divisor coefficient of the source's equation (4.19). Then
--
--   $$T_{II}(x,\alpha,U,V)\ \le\ \Bigl(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\Bigr)\Bigl(\log\frac{x}{UV}\Bigr)\log\frac{Vx}{U}+\Bigl(0.55\frac{x}{\sqrt U}+0.78\frac{x}{\sqrt V}\Bigr)\log\frac xU .$$
--
--   This is the second half of the source's Section 5: the two terms on the right are exactly the last two terms of Theorem 5.1. The argument writes $\eta_0$ through its dyadic integral representation, applies the subdivision form of the odd bilinear large sieve on each dyadic block, and integrates the resulting $\frac{dW}{W}$ envelope.
--
--   **Note for anyone attacking this** One of the source's intermediate displays in this passage does not come out as written: the third coefficient of the square-root expansion is $1$ rather than $\frac1{\sqrt2}$, since $\sqrt{2q}\cdot\sqrt{\frac{x}{2Wq}}\cdot\sqrt x=x\sqrt{\frac{2q}{2Wq}}=\frac x{\sqrt W}$. The statement above is the source's, unmodified.
--
--   **Formalization Note** The Type II sum and the centred coefficient are the platform definitions imported from `Def_TaoFivePrimes_Theorem51Sums`; the double sum is over all natural numbers, made finite by the compact support of $\eta_0$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, proof of Theorem 5.1, the Type II estimate (the last two terms)

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeII_envelope
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 0.78 * x / Real.sqrt V) * Real.log (x / U) := by sorry
