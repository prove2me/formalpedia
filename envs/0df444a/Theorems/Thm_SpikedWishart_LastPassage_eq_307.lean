-- Prove2me | Theorems.Thm_SpikedWishart_LastPassage_eq_307
-- name    : SpikedWishart.LastPassage.eq_307
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:48.429025+00:00
-- url     : https://prove2.me/theorems/550c7e22-92b2-47e4-998b-445212ce1bc8
-- title:
--   (307), p. 1692 — P(L(N, M) ≤ x) = (1/C)∫_{[0,x]^N} det(e^{−Mπ_iξ_j})/V(π) · V(ξ) Π ξ_j^{M−N} dξ
-- statement:
--   Let $1 \le N \le M$ and let $\pi_1,\ldots,\pi_N$ be pairwise distinct positive numbers. Let $X(i,j)$, $1\le i\le N$, $1\le j\le M$, be independent exponential random variables, $X(i,j)$ of mean $1/(\pi_iM)$, and let $L(N,M)$ be the last passage time (306). Write $V(\xi) = \prod_{i<j}(\xi_j - \xi_i)$ for the Vandermonde determinant and
--   $$w(\xi) = \frac{\det\big(e^{-M\pi_i\xi_j}\big)_{1\le i,j\le N}}{V(\pi)}\, V(\xi) \prod_{j=1}^N \xi_j^{M-N}, \qquad C = \int_{(0,\infty)^N} w(\xi)\, d\xi.$$
--   Then for every real $x$,
--   $$\mathbb P\big(L(N,M) \le x\big) = \frac1C \int_0^x\!\!\cdots\!\int_0^x w(\xi)\, d\xi_1\cdots d\xi_N.$$
--
--   The right-hand side is the distribution function of the largest eigenvalue of the complex sample covariance matrix with population eigenvalues $\pi_j^{-1}$ (formula (61)), so this is the analytic content of Proposition 6.1.
--
--   **Formalization Note** The page's $1/C$ is a normalising constant that it does not write out; it is taken here to be the integral of the same integrand over $(0,\infty)^N$, which is the reading under which the right-hand side is a distribution function. The ratio $\det(e^{-M\pi_i\xi_j})/V(\pi)$ requires $V(\pi) \ne 0$, so the $\pi_i$ are assumed pairwise distinct (the equal case is a limit). The bound $M \ge N$ is the page's. Any sign convention for $V$ cancels between the integral and $C$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1692, (307)

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_LPP

namespace SpikedWishart.LastPassage

open MeasureTheory ProbabilityTheory

/-- (307): for `M ≥ N` and pairwise distinct positive `π`, the exponential last passage time has
distribution function
`P(L(N, M) ≤ x) = (1/C) ∫_{[0,x]^N} det(e^{-M π_i ξ_j}) / V(π) · V(ξ) · ∏_j ξ_j^{M-N} dξ`,
where `C` is the same integral over `(0, ∞)^N` and `V` is the Vandermonde determinant. -/
theorem eq_307 {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ≤ M) (π : Fin N → ℝ)
    (hπ : ∀ i, 0 < π i) (hπinj : Function.Injective π) (x : ℝ) :
    (expLaw π M).real {X | L X ≤ x} =
      (∫ ξ in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          (Matrix.of fun i j => Real.exp (-(M * π i * ξ j))).det / (Matrix.vandermonde π).det *
            (Matrix.vandermonde ξ).det * ∏ j, ξ j ^ (M - N))⁻¹ *
        ∫ ξ in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) x),
          (Matrix.of fun i j => Real.exp (-(M * π i * ξ j))).det / (Matrix.vandermonde π).det *
            (Matrix.vandermonde ξ).det * ∏ j, ξ j ^ (M - N) := by sorry

end SpikedWishart.LastPassage
