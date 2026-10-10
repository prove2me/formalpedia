-- Prove2me | Theorems.Thm_WassFSG_Grad_lemma_2
-- name    : WassFSG.Grad.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:48.118751+00:00
-- url     : https://prove2.me/theorems/218537a6-b692-429d-8111-e15a20557fc5
-- title:
--   Lemma 2 — gradient regularization, |R_{Q,2}(ρ; f) − ρ‖‖∇f‖_*‖_{Q,2}| ≤ ħρ²
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, $\mathbb Q\in\mathcal P_2(\mathcal Z)$ and $\rho\ge0$. Let $f:\mathcal Z\to\mathbb R$ be differentiable with $\hbar$-Lipschitz gradient, $\|\nabla f(\tilde z)-\nabla f(z)\|_*\le\hbar\|\tilde z-z\|$, for some $\hbar>0$. Then
--   $$
--   \big|\mathcal R_{\mathbb Q,2}(\rho;f)-\rho\,\|\|\nabla f\|_*\|_{\mathbb Q,2}\big|\le\hbar\rho^2 .
--   $$
--
--   The 2-Wasserstein regularizer is, up to a second-order term, the gradient-norm regularizer $\rho\|\|\nabla f\|_*\|_{\mathbb Q,2}$. Corollary 6 uses it at $\mathbb Q=\mathbb P_n$ to pass from gradient regularization to 2-Wasserstein DRO.
--
--   **Formalization Note** Stated for a single loss (Assumption 2 for the class $\{f\}$). Since $\mathcal R_{\mathbb Q,2}$ is an extended real, the absolute-value bound is stated as the two inequalities $\mathcal R_{\mathbb Q,2}(\rho;f)\le\rho\|\|\nabla f\|_*\|_{\mathbb Q,2}+\hbar\rho^2$ and $\rho\|\|\nabla f\|_*\|_{\mathbb Q,2}-\hbar\rho^2\le\mathcal R_{\mathbb Q,2}(\rho;f)$; together they say $\mathcal R_{\mathbb Q,2}(\rho;f)$ is finite and are equivalent to the printed bound.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 2, p. 5 (proof App. A, p. 19)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher

open MeasureTheory

namespace WassFSG.Grad

theorem lemma_2 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Q : Measure Z) (hQ : IsP2 Q) (ρ : ℝ) (hρ : 0 ≤ ρ) (f : Z → ℝ) (ħ : ℝ)
    (hf : GradLipBound ħ {f}) :
    regularizer Q ρ f ≤ ((ρ * gradNorm Q f + ħ * ρ ^ 2 : ℝ) : EReal) ∧
      ((ρ * gradNorm Q f - ħ * ρ ^ 2 : ℝ) : EReal) ≤ regularizer Q ρ f := by sorry

end WassFSG.Grad
