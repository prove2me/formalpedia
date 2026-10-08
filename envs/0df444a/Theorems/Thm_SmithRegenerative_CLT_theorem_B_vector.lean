-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_theorem_B_vector
-- name    : SmithRegenerative.CLT.theorem_B_vector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:29.026932+00:00
-- url     : https://prove2.me/theorems/b25722fe-fb6f-46f9-ba54-2f429d64d87a
-- title:
--   §5·4, p. 29 — the M-dimensional form of Anscombe's Theorem B
-- statement:
--   Let $\psi$ and $m_t$ be as in Theorem B: $\psi$ is an unbounded, non-decreasing real function, $m_t$ takes values in the positive integers, and $m_t/\psi(t) \to 1$ in probability. Let
--   $$\mathbf y_j = \left(y^{(1)}_j, \dots, y^{(M)}_j\right), \qquad j = 1, 2, \dots,$$
--   be independent, identically distributed random vectors in $\mathbb R^M$ with square-integrable components, $E y^{(l)}_j = 0$ for all $l$, and covariance matrix $a_{kl} = \operatorname{cov}(y^{(k)}_j, y^{(l)}_j)$. Then the random vector
--   $$\frac{1}{\sqrt{\psi(t)}} \left( \sum_{j=1}^{m_t} y^{(1)}_j, \dots, \sum_{j=1}^{m_t} y^{(M)}_j \right)$$
--   is asymptotically normally distributed, with mean $0$ and covariance matrix $(a_{kl})$, as $t \to \infty$.
--
--   This vector form of Anscombe's theorem is what Smith uses to prove the joint asymptotic normality of several cumulative processes (Theorem 10).
--
--   **Formalization Note** Vectors are elements of the Euclidean space $\mathbb R^M$. "Asymptotically normally distributed" is convergence in distribution (weak convergence of laws) to the centred Gaussian law $\mathcal N(0, a)$. The matrix $a$ is defined as the covariance matrix of $\mathbf y_1$, hence positive semidefinite; the limit may be degenerate and no positivity is assumed. No independence between $m_t$ and the $\mathbf y_j$, nor between the components of $\mathbf y_j$, is assumed.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 29, §5·4, (5·4·3)–(5·4·7) and the italicized conclusion following (5·4·7)

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), §5·4, p. 29 (unnumbered): the `M`-dimensional form of Anscombe's Theorem B.
Let `y_j = (y_j^{(1)}, …, y_j^{(M)})` (`j = 1, 2, …`) be independent, identically distributed
random vectors with `E y_j^{(l)} = 0` and `cov(y_j^{(k)}, y_j^{(l)}) = a_kl` (5·4·3)–(5·4·4), and let
`ψ`, `m_t` be as in Theorem B. Then "the random vector
`(1/√{ψ(t)}){Σ₁^{m_t} y_j^{(1)}, …, Σ₁^{m_t} y_j^{(M)}}` is asymptotically normally distributed,
with covariance matrix `a_kl = cov y_j^{(k)}, y_j^{(l)}`."

**Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin M)`. "Asymptotically normally
distributed with covariance matrix `a`" is convergence in distribution, along real `t → ∞`, to the
centred Gaussian law `multivariateGaussian 0 a` (written as `TendstoInDistribution` with limit
variable `id` on that law). `a` is defined as the covariance matrix of `y_1`, so it is positive
semidefinite and Mathlib's `multivariateGaussian 0 a` is the genuine Gaussian law with covariance
`a` (possibly degenerate). No independence between `m_t` and the `y_j`, and none between the
components of `y_j`, is assumed. `y 0` is unused. -/
theorem theorem_B_vector {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {M : ℕ} (ψ : ℝ → ℝ) (hψ_mono : Monotone ψ) (hψ_unbdd : ¬ BddAbove (Set.range ψ))
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t)) (hm_pos : ∀ t ω, 1 ≤ m t ω)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin M)) (hy_indep : iIndepFun (fun j => y (j + 1)) P)
    (hy_ident : ∀ j, IdentDistrib (y (j + 1)) (y 1) P P)
    (hy_L2 : ∀ l, MemLp (fun ω => y 1 ω l) 2 P) (hy_mean : ∀ l, ∫ ω, y 1 ω l ∂P = 0) :
    TendstoInDistribution
      (fun (t : ℝ) (ω : Ω) => (Real.sqrt (ψ t))⁻¹ • ∑ j ∈ Finset.Icc 1 (m t ω), y j ω)
      atTop id (fun _ => P)
      (multivariateGaussian 0 (covMatrix P (fun l ω => y 1 ω l))) := by sorry

end SmithRegenerative.CLT
