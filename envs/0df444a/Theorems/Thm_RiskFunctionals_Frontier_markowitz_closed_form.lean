-- Prove2me | Theorems.Thm_RiskFunctionals_Frontier_markowitz_closed_form
-- name    : RiskFunctionals.Frontier.markowitz_closed_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:24.048345+00:00
-- url     : https://prove2.me/theorems/76d81ac4-d801-4142-8a1e-e0e9cb5d07d3
-- title:
--   Proposition 4.8 — closed-form mean-variance efficient portfolio $x^*(\mu)$ and the parabolic frontier $\mathbb{V}\mathrm{ar}(Y_\mu)=(\mu^2c-2\mu b+a)/d$
-- statement:
--   Let $\xi=(\xi^{(1)},\dots,\xi^{(M)})$ be a random vector of asset returns with finite second moments on a probability space, $r=\mathbb E\xi$ its vector of expected returns and $C=\mathrm{Cov}(\xi)$ its $M\times M$ covariance matrix. Write $\mathbb 1$ for the all-ones vector. The CAPM problem without a risk-free asset is
--   $$\text{minimize } x^\top Cx\quad\text{subject to}\quad r^\top x=\mu,\quad \mathbb 1^\top x=1, \tag{4.20}$$
--   for a required expected return $\mu\in\mathbb R$. Assume that $C$ is invertible and that $r$ is not a multiple of $\mathbb 1$. Put
--   $$a=r^\top C^{-1}r,\qquad b=r^\top C^{-1}\mathbb 1,\qquad c=\mathbb 1^\top C^{-1}\mathbb 1,\qquad d=ac-b^2, \tag{4.22}$$
--   and
--   $$x^*(\mu)=\mu\Big[\frac cd C^{-1}r-\frac bd C^{-1}\mathbb 1\Big]+\Big[\frac ad C^{-1}\mathbb 1-\frac bd C^{-1}r\Big]. \tag{4.21}$$
--   Then:
--
--   1. for every $\mu$, $x^*(\mu)$ is a solution of (4.20);
--   2. it is the only one: every solution of (4.20) for the return $\mu$ equals $x^*(\mu)$;
--   3. (Two Fund Theorem) for any two different returns $\mu_1\ne\mu_2$, every efficient portfolio (a solution of (4.20) for some $\mu$) is an affine combination $t\,x^*(\mu_1)+(1-t)\,x^*(\mu_2)$, $t\in\mathbb R$;
--   4. the efficient return $Y_\mu=x^*(\mu)^\top\xi$ satisfies
--   $$\mathbb E(Y_\mu)=\mu,\qquad \mathbb{V}\mathrm{ar}(Y_\mu)=\frac{\mu^2c-2\mu b+a}{d}.$$
--
--   So the efficient portfolio is affine-linear in $\mu$, and the variance efficient frontier is a parabola in $\mu$. This is the classical closed-form solution of Markowitz's mean-variance portfolio problem with short selling allowed.
--
--   **Formalization Note** "The solution" is rendered as existence (clause 1) and uniqueness (clause 2) of the global minimizer. The hypothesis "$C$ invertible" is kept as printed; since $C$ is the covariance matrix of $\xi$ (symmetric positive semidefinite), it then is positive definite. "$r$ is not a multiple of $\mathbb 1$" is kept as printed (no real $k$ with $r=k\mathbb 1$), not replaced by $d\ne0$. The book's "the Two Fund Theorem (Theorem 4.5) holds" is clause 3, read in the model (4.20). Assets are indexed by `Fin M`; expectations are Lebesgue integrals and the variance is Mathlib's `variance`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 191, Proposition 4.8, Eqs. (4.20)–(4.22)

import Mathlib
import Definitions.Def_RiskFunctionals_Frontier_MeanVariance

namespace RiskFunctionals.Frontier

open MeasureTheory ProbabilityTheory Matrix

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 191,
Proposition 4.8. Let `ξ = (ξ⁽¹⁾, …, ξ⁽ᴹ⁾)` be a random vector with finite second moments,
`r = 𝔼ξ` and `C = Cov(ξ)`. If `C` is invertible and `r` is not a multiple of `𝟙`, then for every
required return `μ` the problem (4.20) has the unique solution `x*(μ)` of (4.21), with `a, b, c, d`
of (4.22); in particular (Two Fund Theorem) for any two different required returns `μ₁ ≠ μ₂` every
efficient portfolio is an affine combination of `x*(μ₁)` and `x*(μ₂)`; and the efficient return
`Y_μ = x*(μ)ᵀξ` has `𝔼(Y_μ) = μ` and `𝕍ar(Y_μ) = (μ²c − 2μb + a)/d`. -/
theorem markowitz_closed_form {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : ℕ} (ξ : Fin M → Ω → ℝ) (hξ : ∀ m, MemLp (ξ m) 2 P)
    (hC : IsUnit (covMatrix P ξ))
    (hr : ¬ ∃ k : ℝ, meanVector P ξ = fun _ => k) :
    let C := covMatrix P ξ
    let r := meanVector P ξ
    let one : Fin M → ℝ := fun _ => 1
    let a := r ⬝ᵥ C⁻¹ *ᵥ r
    let b := r ⬝ᵥ C⁻¹ *ᵥ one
    let c := one ⬝ᵥ C⁻¹ *ᵥ one
    let d := a * c - b ^ 2
    let xstar : ℝ → Fin M → ℝ := fun μ =>
      μ • ((c / d) • C⁻¹ *ᵥ r - (b / d) • C⁻¹ *ᵥ one) +
        ((a / d) • C⁻¹ *ᵥ one - (b / d) • C⁻¹ *ᵥ r)
    (∀ μ : ℝ, IsSolution420 C r μ (xstar μ)) ∧
    (∀ (μ : ℝ) (x : Fin M → ℝ), IsSolution420 C r μ x → x = xstar μ) ∧
    (∀ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ → ∀ (μ : ℝ) (x : Fin M → ℝ), IsSolution420 C r μ x →
      ∃ t : ℝ, x = t • xstar μ₁ + (1 - t) • xstar μ₂) ∧
    (∀ μ : ℝ, ∫ ω, portfolioReturn ξ (xstar μ) ω ∂P = μ ∧
      variance (portfolioReturn ξ (xstar μ)) P = (μ ^ 2 * c - 2 * μ * b + a) / d) := by sorry

end RiskFunctionals.Frontier
