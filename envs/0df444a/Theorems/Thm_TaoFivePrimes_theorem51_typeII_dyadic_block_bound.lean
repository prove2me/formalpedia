-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_dyadic_block_bound
-- name    : TaoFivePrimes.theorem51_typeII_dyadic_block_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T20:56:39.650249+00:00
-- url     : https://prove2.me/theorems/5b36c013-93ce-45ab-9d11-2430d74f7139
-- title:
--   Tao Section 5: the large sieve bound for a Type II dyadic block
-- statement:
--   **The large sieve bound for a dyadic block of the Type II sum.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$, and let $V\le W\le\frac xU$. With $G(W)$ the dyadic block of the bilinear Type II sum,
--
--   $$G(W)\ \le\ \frac{1.1}{8}\Bigl(\frac1{2\sqrt2}\frac x{\sqrt q}+\frac12\sqrt{xW}+\frac x{\sqrt W}+\sqrt2\,\sqrt{xq}\Bigr)\log W .$$
--
--   This is the arithmetic half of the source's Type II estimate. In that regime both intervals $[\frac{x}{2W},\frac xW]$ and $[\frac W2,W]$ have length at least $2$, so the subdivision form of the odd bilinear large sieve applies with $M=\frac q2$ and gives
--   $$G(W)\le\tfrac12\Bigl(\tfrac12\tfrac W2+\tfrac1\delta\Bigr)^{1/2}\Bigl(\Bigl\lfloor\frac{x}{2Wq}\Bigr\rfloor+1\Bigr)^{1/2}A^{1/2}B^{1/2},$$
--   where $\delta=\inf_{1\le j\le q/2}\|4j\alpha\|_{\mathbb R/\mathbb Z}\ge\frac1{2q}$, $A$ counts the odd $d\in[\frac x{2W},\frac xW]$ and $B=\sum_{w\in[W/2,W]\text{ odd}}\log^2w$, using $|g(w)|\le\frac12\log w$. The counting bounds $A\le\frac{x}{4W}+1$ and $B\le(\frac W4+1)\log^2W$ then give $A\le\frac{1.1}4\frac xW$ and $B\le\frac{1.1}4W\log^2W$, and the displayed envelope follows from the square-root expansion $\sqrt{\frac W4+2q}\sqrt{\frac x{2Wq}+1}\sqrt x\le\frac1{2\sqrt2}\frac x{\sqrt q}+\frac12\sqrt{xW}+\frac x{\sqrt W}+\sqrt2\sqrt{xq}$.
--
--   All four ingredients are public and proved on the platform: `TaoFivePrimes.large_sieve_subdivision`, `TaoFivePrimes.typeII_counting_bounds`, `TaoFivePrimes.typeII_pointwise` and `TaoFivePrimes.typeII_sqrt_expansion`.
--
--   **Formalization Note** The coefficient of $\frac x{\sqrt W}$ is $1$, which is what the square-root expansion gives; the source prints $\frac1{\sqrt2}$, and that is the origin of the $1.1$ rather than $0.78$ in the final Type II constant.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, the bound for F(W) by the odd bilinear large sieve

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open MeasureTheory

theorem TaoFivePrimes.theorem51_typeII_dyadic_block_bound
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (W : ℝ) (hW : W ∈ Set.Icc V (x / U)) :
    ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q)
          + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
          + Real.sqrt 2 * Real.sqrt (x * (q : ℝ))) * Real.log W := by sorry
