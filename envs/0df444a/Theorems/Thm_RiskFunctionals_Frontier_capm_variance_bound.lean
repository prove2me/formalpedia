-- Prove2me | Theorems.Thm_RiskFunctionals_Frontier_capm_variance_bound
-- name    : RiskFunctionals.Frontier.capm_variance_bound
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:14.337443+00:00
-- url     : https://prove2.me/theorems/5886ba9f-7ed6-4f5e-b648-c28da42e2586
-- title:
--   Proposition 4.10 (ii), as printed — the CAPM variance bound, with equality iff $\mathbb{C}\mathrm{orr}(Y_x,Y_+)=1$, i.e. iff $x$ is efficient
-- statement:
--   Let $\tilde\xi=(\xi_1,\dots,\xi_M)$ be a random vector of risky returns with finite second moments, $\tilde r=\mathbb E\tilde\xi$, and $\tilde C=\mathrm{Cov}(\tilde\xi)$ invertible. A risk-free asset has the constant return $r_0$, with $\tilde r\ne r_0\mathbb 1$ and $\mathbb 1^\top\tilde C^{-1}(\tilde r-r_0\mathbb 1)\ne0$. The market portfolio holds nothing in the risk-free asset and $\tilde x_+=\tilde C^{-1}(\tilde r-r_0\mathbb 1)/\mathbb 1^\top\tilde C^{-1}(\tilde r-r_0\mathbb 1)$ in the risky assets; its return is $Y_+=\tilde x_+^\top\tilde\xi$, with $\mu_+=\mathbb E(Y_+)$ and $\sigma_+^2=\mathbb{V}\mathrm{ar}(Y_+)$.
--
--   Let $x=(x_0,\tilde x)$ be any portfolio with $x_0+\mathbb 1^\top\tilde x=1$ and return $Y_x=x_0r_0+\tilde x^\top\tilde\xi$. Then:
--
--   1. $$\mathbb{V}\mathrm{ar}(Y_x)\ \ge\ \Big(\frac{\mathbb E(Y_x)-r_0}{\mu_+-r_0}\Big)^2\sigma_+^2 ;$$
--   2. equality holds if and only if $x$ is **efficient**, i.e. a solution of the CAPM problem (4.23) (minimize $\tfrac12\tilde x^\top\tilde C\tilde x$ subject to $\tilde r^\top\tilde x+r_0x_0=\mu$, $\mathbb 1^\top\tilde x+x_0=1$) for some $\mu$;
--   3. if $\mathbb{V}\mathrm{ar}(Y_x)>0$, equality holds if and only if $\mathbb{C}\mathrm{orr}(Y_x,Y_+)=1$.
--
--   In the risk–return plane, no portfolio lies above the line through the risk-free asset and the market portfolio (the capital market line), and the efficient portfolios are the ones on it.
--
--   **Formalization Note** Stated as printed. Finding F4 records that clause 3 is false as printed: a portfolio short in the market portfolio attains equality with correlation $-1$ (one risky asset with $\tilde r=2$, $\tilde C=1$, $r_0=1$, and $x=(2,-1)$); the variant `RiskFunctionals.Frontier.capm_variance_bound_corrected` replaces $\mathbb{C}\mathrm{orr}=1$ by $|\mathbb{C}\mathrm{orr}|=1$. The book's "i.e. if the portfolio is efficient" is clause 2. The correlation is undefined when $\mathbb{V}\mathrm{ar}(Y_x)=0$ (the risk-free portfolio), so clause 3 assumes $\mathbb{V}\mathrm{ar}(Y_x)>0$. The budget constraint and the nondegeneracy hypotheses ($\tilde C$ invertible, $\tilde r\ne r_0\mathbb 1$, $\mathbb 1^\top\tilde C^{-1}(\tilde r-r_0\mathbb 1)\ne0$) are implicit on the page; under them $\mu_+\ne r_0$ and $\sigma_+^2>0$. Assets are indexed by `Fin M`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 195, Proposition 4.10 (ii)

import Mathlib
import Definitions.Def_RiskFunctionals_Frontier_MeanVariance

namespace RiskFunctionals.Frontier

open MeasureTheory ProbabilityTheory Matrix

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 195,
Proposition 4.10 (ii), as printed. In the model (4.23) (risky assets `ξ̃` with finite second
moments, `r̃ = 𝔼ξ̃`, `C̃ = Cov(ξ̃)` invertible, risk-free return `r₀`, `r̃ ≠ r₀𝟙`), with the market
portfolio `x₊` (risky part `C̃⁻¹(r̃ − r₀𝟙)/𝟙ᵀC̃⁻¹(r̃ − r₀𝟙)`), `Y₊ = x₊ᵀξ̃`, `μ₊ = 𝔼(Y₊)`,
`σ₊² = 𝕍ar(Y₊)`, every portfolio `x = (x₀, x̃)`, `x₀ + 𝟙ᵀx̃ = 1`, with return `Y_x = x₀r₀ + x̃ᵀξ̃`
satisfies `𝕍ar(Y_x) ≥ ((𝔼(Y_x) − r₀)/(μ₊ − r₀))² σ₊²`; equality holds if and only if
`ℂorr(Y_x, Y₊) = 1` (stated where `ℂorr` is defined, `𝕍ar(Y_x) > 0`), i.e. if and only if the
portfolio is efficient (a solution of (4.23) for some `μ`). -/
theorem capm_variance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : ℕ} (ξ : Fin M → Ω → ℝ) (hξ : ∀ m, MemLp (ξ m) 2 P)
    (r₀ : ℝ) (hC : IsUnit (covMatrix P ξ)) (hq : meanVector P ξ ≠ fun _ => r₀) :
    let C := covMatrix P ξ
    let r := meanVector P ξ
    let one : Fin M → ℝ := fun _ => 1
    let v := r - r₀ • one
    let xplus : Fin M → ℝ := (1 / (one ⬝ᵥ C⁻¹ *ᵥ v)) • C⁻¹ *ᵥ v
    let Yplus : Ω → ℝ := portfolioReturn ξ xplus
    let μplus : ℝ := ∫ ω, Yplus ω ∂P
    let σplus2 : ℝ := variance Yplus P
    one ⬝ᵥ C⁻¹ *ᵥ v ≠ 0 →
    ∀ (x₀ : ℝ) (x : Fin M → ℝ), one ⬝ᵥ x + x₀ = 1 →
      let Yx : Ω → ℝ := riskFreeReturn r₀ ξ x₀ x
      let bound : ℝ := ((∫ ω, Yx ω ∂P - r₀) / (μplus - r₀)) ^ 2 * σplus2
      bound ≤ variance Yx P ∧
      (variance Yx P = bound ↔ ∃ μ : ℝ, IsSolution423 C r r₀ μ x₀ x) ∧
      (0 < variance Yx P → (variance Yx P = bound ↔ correlation P Yx Yplus = 1)) := by sorry

end RiskFunctionals.Frontier
