-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_block_summation
-- name    : TaoFivePrimes.theorem51_typeI_block_summation
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:47:23.341863+00:00
-- url     : https://prove2.me/theorems/7b6bb2d9-e6fa-4629-80e7-f3a34b9ff416
-- title:
--   Tao Section 5: summing the Type I envelope over blocks
-- statement:
--   **Summing the Type I pointwise envelope.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, let $x>0$ and $U,V\ge40$ with $UV\le\frac x4$, and let $W$ be any nonnegative function on the positive odd integers $d\le UV$ satisfying the pointwise envelope
--
--   $$W(d)\ \le\ \min\Bigl(\frac12\frac xd\log x+4(\log2)\log 2x,\ \frac{4(\log2)\log 2x}{|\sin(2\pi d\alpha)|}\Bigr)$$
--
--   (the second alternative dropped when the sine vanishes). Then
--
--   $$\sum_{\substack{d\le UV\\ d\text{ odd}}}W(d)\ \le\ 0.5\,\frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+0.89\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x).$$
--
--   This is the combinatorial half of the source's Type I estimate, separated from the analysis that produces the envelope. The argument splits the range of $d$: for $d\le\frac q2$ one has $\|4d\alpha\|_{\mathbb R/\mathbb Z}\ge\frac1q-\frac{q/2}{q^2}=\frac1{2q}$, hence $\frac1{|\sin(2\pi d\alpha)|}\le2q$, and the odd-restricted Vinogradov lemma bounds that contribution; for each subsequent block $2jq+\frac q2<d\le2(j+1)q+\frac q2$ the same lemma applies with the first alternative frozen at the left endpoint of the block, and the resulting harmonic sum over blocks is estimated by an integral test.
--
--   **Why the additive 4** The integral test compares the decreasing summand with the integral over the preceding block of length $2q$, which covers the blocks $j\ge1$ but not $j=0$; the uncovered term is $\frac{x}{q/2}=\frac{x}{2q}\cdot4$. At $q=4$, $UV=40$ the sum $\sum_{0\le j\le4}\frac{x}{2\cdot4j+2}$ equals $0.7235x$ while $\frac x8\log24=0.3973x$. The statement above carries the restored term; the source's display omits it.
--
--   **Formalization Note** $W$ is an arbitrary nonnegative function on $\mathbb N$ constrained only on the positive odd $d\le UV$, so the statement is exactly the passage from the envelope to the two terms and carries no information about the exponential sums themselves. The index set is the platform's `theorem51Divisors U V`.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, estimation of the Type I sum, the block decomposition and integral test, with the first term weakened to match that integral test

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeI_block_summation
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUV : U * V ≤ x / 4)
    (W : ℕ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V,
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
                else min ((1 / 2) * (x / (d : ℝ)) * Real.log x
                    + 4 * Real.log 2 * Real.log (2 * x))
                  (4 * Real.log 2 * Real.log (2 * x)
                    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      ≤ 0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by sorry
