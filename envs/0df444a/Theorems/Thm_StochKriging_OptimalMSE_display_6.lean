-- Prove2me | Theorems.Thm_StochKriging_OptimalMSE_display_6
-- name    : StochKriging.OptimalMSE.display_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:05.356831+00:00
-- url     : https://prove2.me/theorems/af37a840-c455-443b-ac5f-aed93146f093
-- title:
--   §2, display (6), p. 364 — the stochastic kriging predictor is the unique MSE-optimal predictor of the form (5)
-- statement:
--   Work in the second-order stochastic kriging model: outputs $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$ with square-integrable, mean-zero field $\mathsf M$ and noise $\varepsilon$, field and noise uncorrelated, and noise correlation across design points allowed (CRN). Let $(\mathbf x_i,n_i)_{i=1}^k$ be a design with every $n_i\ge1$, let $\bar{\mathcal Y}$ be the vector of sample means, and let $\Sigma_{\mathsf M}$, $\Sigma_\varepsilon$ and $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)$ be the covariance matrices and vector of §2. Assume $\Sigma_{\mathsf M}+\Sigma_\varepsilon$ is positive definite, and put
--   $$\lambda^\star=[\Sigma_{\mathsf M}+\Sigma_\varepsilon]^{-1}\Sigma_{\mathsf M}(\mathbf x_0,\cdot),\qquad \lambda_0^\star=\beta_0-\beta_0\,\lambda^{\star\top}\mathbf 1_k .$$
--   Then, for every prediction point $\mathbf x_0$:
--   1. the stochastic kriging predictor $\widehat{\mathsf Y}(\mathbf x_0)=\beta_0+\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top[\Sigma_{\mathsf M}+\Sigma_\varepsilon]^{-1}(\bar{\mathcal Y}-\beta_0\mathbf 1_k)$ is the linear predictor $\lambda_0^\star+\lambda^{\star\top}\bar{\mathcal Y}$ of the form (5);
--   2. it has the smallest mean squared error for $\mathsf Y(\mathbf x_0)=\beta_0+\mathsf M(\mathbf x_0)$ among all predictors of the form (5):
--   $$\mathrm E\big[(\widehat{\mathsf Y}(\mathbf x_0)-\mathsf Y(\mathbf x_0))^2\big]\le\mathrm E\big[(\lambda_0+\lambda^\top\bar{\mathcal Y}-\mathsf Y(\mathbf x_0))^2\big]\quad\text{for all }\lambda_0\in\mathbb R,\ \lambda\in\mathbb R^k;$$
--   3. it is the only one: any weights $(\lambda_0,\lambda)$ achieving an MSE no larger than that of $\widehat{\mathsf Y}(\mathbf x_0)$ equal $(\lambda_0^\star,\lambda^\star)$.
--
--   This is the paper's display (6), which defines **stochastic kriging**: the classical kriging predictor with the covariance of the data enlarged by the intrinsic covariance $\Sigma_\varepsilon$.
--
--   **Formalization Note** The weights range over all of $\mathbb R\times\mathbb R^k$, with no unbiasedness constraint. No Gaussianity, no independence across replications and no "no CRN" assumption is made; $\Sigma_\varepsilon$ is a general covariance matrix. The uncorrelatedness of field and noise and the finite second moments are added (§2 uses them implicitly). Positive definiteness of $\Sigma_{\mathsf M}+\Sigma_\varepsilon$ makes the inverse in (6) genuine; the sum is always positive semidefinite, being the covariance matrix of $\bar{\mathcal Y}$, so the hypothesis says exactly that it is invertible.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 364, §2, display (6)

import Mathlib
import Definitions.Def_StochKriging_OptimalMSE_Model

open MeasureTheory ProbabilityTheory Matrix

namespace StochKriging.OptimalMSE

/-- Display (6), p. 364: the stochastic kriging predictor `Ŷ(x₀)` is a predictor of the form (5),
with weights `λ = [ΣM + Σε]⁻¹ ΣM(x₀, ·)` and `λ₀ = β₀ − β₀ λᵀ1_k`; it has the smallest MSE for
`Y(x₀)` among all predictors of the form (5); and these weights are the only minimizers. -/
theorem display_6 {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (β₀ : ℝ) (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ)
    (hmodel : IsModel P M ε) (hn : ∀ i, 1 ≤ n i)
    (hSig : (SigmaM P M x + SigmaEps P ε x n).PosDef) (x₀ : X) :
    (∀ ω, skPredictor P β₀ M ε x n x₀ ω =
        linPred
          (β₀ - β₀ * (((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ⬝ᵥ
            fun _ => 1))
          ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀)
          (sampleMean β₀ M ε x n) ω) ∧
    (∀ (l₀ : ℝ) (l : Fin k → ℝ),
        mse P (skPredictor P β₀ M ε x n x₀) (target β₀ M x₀) ≤
          mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀)) ∧
    (∀ (l₀ : ℝ) (l : Fin k → ℝ),
        mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀) ≤
            mse P (skPredictor P β₀ M ε x n x₀) (target β₀ M x₀) →
          l = (SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀ ∧
          l₀ = β₀ - β₀ * (((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ⬝ᵥ
            fun _ => 1)) := by sorry

end StochKriging.OptimalMSE
