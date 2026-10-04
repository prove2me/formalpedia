-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_block_summation_as_proved
-- name    : TaoFivePrimes.theorem51_typeI_block_summation_as_proved
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:13:50.065582+00:00
-- url     : https://prove2.me/theorems/697fcba5-783b-4f44-a5a3-b3b9a82dc021
-- title:
--   Tao Section 5: summing the Type I envelope, as the argument gives it
-- statement:
--   **Summing the Type I pointwise envelope, with the constants the argument gives.** Let $q\ge4$ with $(a,q)=1$, let $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, let $x>0$ and $U,V\ge40$ with $UV\le\frac x4$, and let $W$ be any nonnegative function satisfying, for every positive odd $d\le UV$,
--
--   $$W(d)\ \le\ \min\Bigl(\frac12\frac xd\log x+4(\log2)\log2x,\ \frac{4(\log2)\log2x}{|\sin(2\pi d\alpha)|}\Bigr)$$
--
--   (the second alternative dropped when the sine vanishes). Then
--
--   $$\sum_{\substack{d\le UV\\ d\text{ odd}}}W(d)\ \le\ \frac xq(\log x)\Bigl(\log\Bigl(\frac{2UV}{q}+4\Bigr)+4\Bigr)+1.78\Bigl(UV+\frac52q\Bigr)(8+\log q)\log(2x).$$
--
--   This is the combinatorial half of the source's Type I estimate, separated from the analysis that produces the envelope, and with the two constants its own chain yields. Writing $C=4(\log2)\log2x$, the range of $d$ splits as follows. For $d\le\frac q2$ one has $\|4d\alpha\|_{\mathbb R/\mathbb Z}\ge\frac1q-\frac{q/2}{q^2}=\frac1{2q}$, hence $\frac{1}{|\sin(2\pi d\alpha)|}\le2q$ and $W(d)\le\min(2qC,\frac{C}{|\sin|})$, and the odd-restricted Vinogradov lemma bounds that contribution by $2qC+\frac1\pi Cq\log4q$. Each subsequent block $2jq+\frac q2<d\le2(j+1)q+\frac q2$, $0\le j\le\frac{UV}{2q}-\frac14$, has length exactly $2q$, so the same lemma applies with prefactor $2$ and the first alternative frozen at the block's left endpoint, giving $2\frac{x}{2jq+q/2}\log x+4C+\frac4\pi Cq\log4q$. Summing the harmonic part by the integral test — including its $j=0$ term — produces the first term, and the rest is bounded by $\frac1\pi C(2UV+5q)(\pi+\log4q)$, which is at most $1.78(UV+\frac52q)(8+\log q)\log2x$ since $\frac{8\log2}\pi\le1.78$ and $\pi+\log4q\le8+\log q$.
--
--   **Formalization Note** $W$ is an arbitrary nonnegative function on $\mathbb N$, constrained only on the positive odd $d\le UV$, so the statement is exactly the passage from the envelope to the two terms and says nothing about exponential sums. The index set is the platform's `theorem51Divisors U V`, and the sine is written $\sin(\pi\cdot2\alpha\cdot d)$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, estimation of the Type I sum, the block decomposition and integral test, with both constants as that argument yields them

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.theorem51_typeI_block_summation_as_proved
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
      ≤ (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by sorry
