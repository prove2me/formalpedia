-- Prove2me | Theorems.Thm_TaoFivePrimes_typeI_block_sum_bound
-- name    : TaoFivePrimes.typeI_block_sum_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:25:04.282243+00:00
-- url     : https://prove2.me/theorems/9e5e1ed4-4f71-4ea2-a3b7-3e9210d2f756
-- title:
--   Tao Section 5: the integral test for the Type I block sum $\sum_j x/(2jq+q/2)$
-- statement:
--   Let $x\ge0$, $q>0$ and $M$ be reals, and let $J$ be a natural number with $J\le\frac{M}{2q}-\frac14$. Then
--
--   $$\sum_{j=0}^{J}\frac{x}{2jq+\tfrac q2}\ \le\ \frac{x}{2q}\left(\log\Bigl(\frac{2M}{q}+4\Bigr)+4\right).$$
--
--   This is the block sum that appears when the Type I sum of the source's minor-arc theorem is cut into blocks $2jq+\tfrac q2<d\le 2(j+1)q+\tfrac q2$ of length $2q$: on the $j$-th block the weight $x/d$ is bounded by its value at the left endpoint, and what remains is exactly the sum above, with $M=UV$ the length of the divisor range. The bound is the integral test applied to $\sum_j\frac1{4j+1}$, whose partial sums are $1+\tfrac14\log(4J+1)$ up to the first term.
--
--   **Deviation from the source** The source's display asserts the same bound *without* the additive $4$, namely $\sum_j\frac{x}{2jq+q/2}\le\frac{x}{2q}\log\bigl(\frac{2M}{q}+4\bigr)$. That cannot hold in general: the $j=0$ term alone is $\frac{x}{q/2}=\frac{x}{2q}\cdot4$, so the claimed right-hand side is already exceeded whenever $\log(\frac{2M}{q}+4)<4$, that is whenever $M/q<\tfrac12(e^4-4)\approx25.3$. For a concrete instance take $q=1$, $M=10$, so that $J=4$: the left-hand side is $2.8937\,x$ while the source's right-hand side is $\tfrac x2\log24=1.5890\,x$. The additive $4$ above is what the integral test actually gives, and the source's downstream estimate has room for it in its remaining terms; the correction is recorded here rather than propagated silently.
--
--   **Formalization Note** The summation index runs over `Finset.range (J+1)`, i.e. $0\le j\le J$, and the hypothesis $J\le\frac{M}{2q}-\frac14$ is what the source's condition on the block index gives. No lower bound on $M$ is assumed: the hypothesis on $J$ already forces $M\ge q/2$, so the logarithm is taken at a value $\ge5$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type I sum", the display beginning "By the integral test, one has" that precedes equation (ti-p); the additive constant 4 is a correction, see the Deviation note

import Mathlib

open Finset

theorem TaoFivePrimes.typeI_block_sum_bound (x q M : ℝ) (hx : 0 ≤ x) (hq : 0 < q)
    (J : ℕ) (hJ : (J : ℝ) ≤ M / (2 * q) - 1 / 4) :
    (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      ≤ (x / (2 * q)) * (Real.log (2 * M / q + 4) + 4) := by sorry
