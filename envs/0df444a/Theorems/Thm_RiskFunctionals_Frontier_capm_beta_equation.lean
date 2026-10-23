-- Prove2me | Theorems.Thm_RiskFunctionals_Frontier_capm_beta_equation
-- name    : RiskFunctionals.Frontier.capm_beta_equation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:12.763835+00:00
-- url     : https://prove2.me/theorems/fb4f569c-cf43-45d7-a538-60c1b69900ad
-- title:
--   Proposition 4.10 (i) — the CAPM equation $\mathbb E(Y_x)=r_0+\beta(x)(\mu_+-r_0)$
-- statement:
--   Let $\tilde\xi=(\xi_1,\dots,\xi_M)$ be a random vector of risky returns with finite second moments, $\tilde r=\mathbb E\tilde\xi$, and $\tilde C=\mathrm{Cov}(\tilde\xi)$ invertible. A risk-free asset has the constant return $r_0$, with $\tilde r\ne r_0\mathbb 1$ and $\mathbb 1^\top\tilde C^{-1}(\tilde r-r_0\mathbb 1)\ne0$. The **market portfolio** holds nothing in the risk-free asset and
--   $$\tilde x_+=\frac{\tilde C^{-1}(\tilde r-r_0\mathbb 1)}{\mathbb 1^\top\tilde C^{-1}(\tilde r-r_0\mathbb 1)}$$
--   in the risky assets; its return is $Y_+=\tilde x_+^\top\tilde\xi$ and its expected return $\mu_+=\mathbb E(Y_+)$.
--
--   For any portfolio $x=(x_0,\tilde x)$ satisfying the budget constraint $x_0+\mathbb 1^\top\tilde x=1$, with return $Y_x=x_0r_0+\tilde x^\top\tilde\xi$,
--   $$\mathbb E(Y_x)=r_0+\beta(x)\,(\mu_+-r_0),\qquad \beta(x)=\frac{\mathbb{C}\mathrm{ov}(Y_x,Y_+)}{\mathbb{V}\mathrm{ar}(Y_+)}.$$
--
--   This is the fundamental equation (4.25) of the capital asset pricing model: the excess expected return of any portfolio is its beta times the excess expected return of the market portfolio.
--
--   **Formalization Note** The page's "for any portfolio $x$" is read in the model (4.23), so the budget constraint $x_0+\mathbb 1^\top\tilde x=1$ is a hypothesis (the book's proof uses it). Invertibility of $\tilde C$, $\tilde r\ne r_0\mathbb 1$ and $\mathbb 1^\top\tilde C^{-1}(\tilde r-r_0\mathbb 1)\ne0$ are implicit on the page, which writes $\tilde C^{-1}$ and divides by the last quantity; under them $\mathbb{V}\mathrm{ar}(Y_+)>0$, so the division in $\beta(x)$ is genuine. Covariance and variance are Mathlib's; assets are indexed by `Fin M`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 195, Proposition 4.10 (i), Eq. (4.25)

import Mathlib
import Definitions.Def_RiskFunctionals_Frontier_MeanVariance

namespace RiskFunctionals.Frontier

open MeasureTheory ProbabilityTheory Matrix

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 195,
Proposition 4.10 (i), the CAPM equation (4.25). In the model (4.23) (risky assets `ξ̃` with finite
second moments, `r̃ = 𝔼ξ̃`, `C̃ = Cov(ξ̃)` invertible, risk-free return `r₀`, `r̃ ≠ r₀𝟙`), let
`x₊ = C̃⁻¹(r̃ − r₀𝟙)/𝟙ᵀC̃⁻¹(r̃ − r₀𝟙)` be the risky part of the market portfolio (its risk-free
part is `0`), `Y₊ = x₊ᵀξ̃` its return, `μ₊ = 𝔼(Y₊)`. For any portfolio `x = (x₀, x̃)`,
`x₀ + 𝟙ᵀx̃ = 1`, with return `Y_x = x₀r₀ + x̃ᵀξ̃`:
`𝔼(Y_x) = r₀ + β(x)(μ₊ − r₀)`, `β(x) = ℂov(Y_x, Y₊)/𝕍ar(Y₊)`.
The page divides by `𝟙ᵀC̃⁻¹(r̃ − r₀𝟙)`; its nonvanishing is the hypothesis of the clause. -/
theorem capm_beta_equation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : ℕ} (ξ : Fin M → Ω → ℝ) (hξ : ∀ m, MemLp (ξ m) 2 P)
    (r₀ : ℝ) (hC : IsUnit (covMatrix P ξ)) (hq : meanVector P ξ ≠ fun _ => r₀) :
    let C := covMatrix P ξ
    let r := meanVector P ξ
    let one : Fin M → ℝ := fun _ => 1
    let v := r - r₀ • one
    let xplus : Fin M → ℝ := (1 / (one ⬝ᵥ C⁻¹ *ᵥ v)) • C⁻¹ *ᵥ v
    let Yplus : Ω → ℝ := portfolioReturn ξ xplus
    let μplus : ℝ := ∫ ω, Yplus ω ∂P
    one ⬝ᵥ C⁻¹ *ᵥ v ≠ 0 →
    ∀ (x₀ : ℝ) (x : Fin M → ℝ), one ⬝ᵥ x + x₀ = 1 →
      ∫ ω, riskFreeReturn r₀ ξ x₀ x ω ∂P =
        r₀ + (covariance (riskFreeReturn r₀ ξ x₀ x) Yplus P / variance Yplus P) * (μplus - r₀) := by sorry

end RiskFunctionals.Frontier
