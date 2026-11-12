-- Prove2me | Theorems.Thm_SubnormalCover_minFac_pred_mul_prod_le
-- name    : SubnormalCover.minFac_pred_mul_prod_le
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:46:45.654295+00:00
-- url     : https://prove2.me/theorems/340777ea-dd3f-4767-944d-6bdb8379a0f5
-- title:
--   An arithmetic inequality between the least and greatest prime factors
-- statement:
--   A purely arithmetic inequality. Let $N\ge 2$ and let $p_1<\dots<p_r$ be the distinct prime divisors of $N$, so that $p_*=p_1$ is the smallest and $p^{*}=p_r$ the largest. Then
--   $$p^{*}\prod_{t=1}^{r}\frac{p_t-1}{p_t}\;\ge\;p_*-1 .$$
--   The proof is a downward induction: $p_r\prod_{t\le r}\frac{p_t-1}{p_t}=(p_r-1)\prod_{t<r}\frac{p_t-1}{p_t}\ge p_{r-1}\prod_{t<r}\frac{p_t-1}{p_t}$, since $p_r>p_{r-1}$ forces $p_r-1\ge p_{r-1}$; iterating down to $t=1$ leaves $p_1\cdot\frac{p_1-1}{p_1}=p_1-1$.
--
--   *Formalization note.* Denominators are cleared, so the statement is the $\mathbb{N}$-inequality $(p_*-1)\prod_{p\mid N}p\le p^{*}\prod_{p\mid N}(p-1)$; all truncated subtractions are exact ($\texttt{Nat.minFac }N\ge 2$ and every $p\ge 2$). The hypothesis $2\le N$ is essential rather than cosmetic: at $N=0$ Mathlib's conventions ($\texttt{minFac }0=2$, $\texttt{primeFactors }0=\varnothing$, $\texttt{maxPrimeFac }0=0$) make the inequality read $1\le 0$, which is false.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Sun, proof of Theorem 4.3(i): the chain $p_r\prod_{t=1}^r\frac{p_t-1}{p_t}\ge p_{r-1}\prod_{t=1}^{r-1}\frac{p_t-1}{p_t}\ge\cdots\ge p_1\frac{p_1-1}{p_1}=p_*-1$ (page 172)

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

namespace SubnormalCover

open BFFPyramidal

theorem minFac_pred_mul_prod_le {N : ℕ} (hN : 2 ≤ N) :
    (Nat.minFac N - 1) * ∏ p ∈ N.primeFactors, p
      ≤ maxPrimeFac N * ∏ p ∈ N.primeFactors, (p - 1) := by
  sorry

end SubnormalCover
