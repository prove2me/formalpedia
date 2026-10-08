-- Prove2me | Theorems.Thm_StochKriging_OptimalMSE_display_7
-- name    : StochKriging.OptimalMSE.display_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:51.795651+00:00
-- url     : https://prove2.me/theorems/92a5ff1e-1448-4343-8b19-d5853d1dfdb3
-- title:
--   §2, display (7), p. 364 — the optimal MSE equals the kriging MSE plus a positive definite form in Σ_M(x₀,·)
-- statement:
--   Fix the number $k$ of design points. There is a rule $\Xi$ that assigns to every pair $(A,B)$ of positive definite $k\times k$ matrices a positive definite matrix $\Xi(A,B)$, such that the following holds in every second-order stochastic kriging model.
--
--   Let $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$ with square-integrable, mean-zero field $\mathsf M$ and noise $\varepsilon$, field and noise uncorrelated, and noise correlation across design points allowed (CRN). Let $(\mathbf x_i,n_i)_{i=1}^k$ be a design with every $n_i\ge1$, let $\bar{\mathcal Y}$ be the vector of sample means, and assume the covariance matrices $\Sigma_{\mathsf M}$ and $\Sigma_\varepsilon$ of §2 are both positive definite. Then for every prediction point $\mathbf x_0$ the optimal MSE over the linear predictors (5),
--   $$\mathrm{MSE}^\star=\inf_{(\lambda_0,\lambda)\in\mathbb R\times\mathbb R^k}\mathrm E\big[(\lambda_0+\lambda^\top\bar{\mathcal Y}-\beta_0-\mathsf M(\mathbf x_0))^2\big],$$
--   satisfies
--   $$\begin{aligned}\mathrm{MSE}^\star&=\Sigma_{\mathsf M}(\mathbf x_0,\mathbf x_0)-\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top[\Sigma_{\mathsf M}+\Sigma_\varepsilon]^{-1}\Sigma_{\mathsf M}(\mathbf x_0,\cdot)\\&=\Big[\Sigma_{\mathsf M}(\mathbf x_0,\mathbf x_0)-\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top\Sigma_{\mathsf M}^{-1}\Sigma_{\mathsf M}(\mathbf x_0,\cdot)\Big]+\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top\,\Xi(\Sigma_{\mathsf M},\Sigma_\varepsilon)\,\Sigma_{\mathsf M}(\mathbf x_0,\cdot),\end{aligned}$$
--   and, whenever $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)\neq0$, $\mathrm{MSE}^\star$ is strictly larger than the bracketed term.
--
--   The bracketed term is the usual kriging MSE, the error of predicting $\mathsf Y(\mathbf x_0)$ from noise-free observations of the field. The result says that intrinsic simulation noise inflates the optimal MSE by a positive definite quadratic form in $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)$, whose matrix depends only on $\Sigma_{\mathsf M}$ and $\Sigma_\varepsilon$, not on $\mathbf x_0$ or on the model beyond these matrices.
--
--   **Formalization Note** "$\Xi$ is a positive definite matrix that depends on $\Sigma_\varepsilon$ and $\Sigma_{\mathsf M}$" is rendered as a function of the two matrices, chosen before the model and the point $\mathbf x_0$; it is not fixed by the statement. The optimal MSE is the infimum over all $(\lambda_0,\lambda)\in\mathbb R\times\mathbb R^k$. The hypotheses $\Sigma_{\mathsf M}\succ0$ and $\Sigma_\varepsilon\succ0$ are not written on the page: the first makes $\Sigma_{\mathsf M}^{-1}$ genuine (Lean's inverse of a singular matrix is $0$), the second is necessary for $\Xi$ to be positive definite (with $\Sigma_\varepsilon=0$ the two lines coincide). The uncorrelatedness of field and noise and the finite second moments are added as in the model. The settings form an arbitrary type, design points are indexed by `Fin k`, and the statement is uniform over all probability spaces and setting types (in fixed universes).
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 364, §2, display (7) and the sentence following it

import Mathlib
import Definitions.Def_StochKriging_OptimalMSE_Model

open MeasureTheory ProbabilityTheory Matrix

namespace StochKriging.OptimalMSE

universe u v

/-- Display (7), p. 364. For `k` design points there is a rule `Ξ` assigning to every pair of
positive definite `k × k` matrices `(ΣM, Σε)` a positive definite matrix `Ξ(ΣM, Σε)` such that, in
every model (3) whose covariance matrices `ΣM` and `Σε` are positive definite, and at every
prediction point `x₀`, the optimal MSE over the linear predictors (5) is
`ΣM(x₀,x₀) − ΣM(x₀,·)ᵀ[ΣM + Σε]⁻¹ΣM(x₀,·)`, equals the kriging MSE
`ΣM(x₀,x₀) − ΣM(x₀,·)ᵀΣM⁻¹ΣM(x₀,·)` plus `ΣM(x₀,·)ᵀ Ξ(ΣM, Σε) ΣM(x₀,·)`, and exceeds the kriging
MSE whenever `ΣM(x₀,·) ≠ 0`. -/
theorem display_7 (k : ℕ) :
    ∃ Ξ : Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ,
      (∀ A B : Matrix (Fin k) (Fin k) ℝ, A.PosDef → B.PosDef → (Ξ A B).PosDef) ∧
      ∀ (Ω : Type u) (X : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (β₀ : ℝ) (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ),
        IsModel P M ε → (∀ i, 1 ≤ n i) →
        (SigmaM P M x).PosDef → (SigmaEps P ε x n).PosDef →
        ∀ x₀ : X,
          optimalMSE P β₀ M ε x n x₀ =
              SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
                ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ∧
          optimalMSE P β₀ M ε x n x₀ =
              (SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
                ((SigmaM P M x)⁻¹ *ᵥ SigmaMCross P M x x₀)) +
              SigmaMCross P M x x₀ ⬝ᵥ
                (Ξ (SigmaM P M x) (SigmaEps P ε x n) *ᵥ SigmaMCross P M x x₀) ∧
          (SigmaMCross P M x x₀ ≠ 0 →
            SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
                ((SigmaM P M x)⁻¹ *ᵥ SigmaMCross P M x x₀) <
              optimalMSE P β₀ M ε x n x₀) := by sorry

end StochKriging.OptimalMSE
