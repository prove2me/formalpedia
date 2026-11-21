-- Prove2me | Theorems.Thm_Titchmarsh_moebius_LSeries_tendsto_inv_riemannZeta_of_riemannHypothesis
-- name    : Titchmarsh.moebius_LSeries_tendsto_inv_riemannZeta_of_riemannHypothesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:47:53.301426+00:00
-- url     : https://prove2.me/theorems/1f27971d-31b2-4507-b290-ea51fe8cf5dc
-- title:
--   Under RH, $\sum\mu(n)n^{-s}\to1/\zeta(s)$ for $\operatorname{Re}s>\tfrac12$
-- statement:
--   Assume the Riemann hypothesis, in Mathlib's form `RiemannHypothesis`. Then for every complex $s$ with $\operatorname{Re}s>\tfrac12$ and $s\neq1$ the Möbius Dirichlet series converges to $1/\zeta(s)$:
--
--   $$\lim_{N\to\infty}\sum_{n=1}^{N}\frac{\mu(n)}{n^{s}}=\frac{1}{\zeta(s)} .$$
--
--   This is the forward direction of Titchmarsh–Heath-Brown, Theorem 14.25(A): under RH, $\sum\mu(n)n^{-s}$ converges, with sum $1/\zeta(s)$, throughout $\operatorname{Re}s>\tfrac12$. For $\operatorname{Re}s\le1$ the convergence is conditional, in the order of the partial sums. It is a genuinely stronger statement than holomorphic continuation of $1/\zeta$.
--
--   **Formalization Note.** The partial sums are ordered sums over $1\le n\le N$. The limit is the complex inverse `(riemannZeta s)⁻¹`. The point $s=1$ is excluded because Lean's `riemannZeta 1` is a junk value (the true reciprocal there is $0$, and $\sum\mu(n)/n=0$ is equivalent to the prime number theorem).
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, §14.25, Theorem 14.25(A) (necessity direction: RH ⇒ Σ μ(n) n^{-s} converges to 1/ζ(s) for σ > 1/2), proved there from (14.25.2) M(x) = O(x^{1/2+ε}) by partial summation. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf

import Mathlib

namespace Titchmarsh

theorem moebius_LSeries_tendsto_inv_riemannZeta_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s))
        Filter.atTop (nhds (riemannZeta s)⁻¹) := by sorry

end Titchmarsh
