-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_cr_limit
-- name    : TwoSidedExp.DemandLimit.cr_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:34.959042+00:00
-- url     : https://prove2.me/theorems/0decbd52-9887-4c9d-822b-c082e93a60ff
-- title:
--   Proof of Theorem 3, p. A7 — limit of the scaled naive CR estimator ĜTE^CR(∞|aC)/λ as λ/τ → 0
-- statement:
--   Let $0<a_C<1$, let $\lambda_n,\tau_n>0$ with $\lambda_n/\tau_n\to0$, and let $s_n$ be a steady state of the customer-randomized design $(a_C,1)$. Then the steady-state naive CR estimator, evaluated at $s_n$, satisfies
--   $$\frac{1}{\lambda_n}\widehat{\mathrm{GTE}}^{\mathrm{CR}}(\infty\mid a_C)\longrightarrow\frac{1}{a_C}\sum_\theta\sum_\gamma a_C\phi_\gamma\,p_{\gamma,1}(\theta,1\mid\rho(1))-\frac{1}{1-a_C}\sum_\theta\sum_\gamma(1-a_C)\phi_\gamma\,p_{\gamma,0}(\theta,1\mid\rho(1)).$$
--
--   Comparing this limit with (46) is how the paper shows that the CR estimator is asymptotically unbiased.
--
--   **Formalization Note** The factors $a_C$ and $1-a_C$ are kept inside the sums as printed.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, Proof of Theorem 3, p. A7, display after (46)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Proof of Theorem 3, p. A7, display after (46): for `0 < aC < 1`, along a sequence of systems
with `λ/τ → 0`, `ĜTE^CR(∞|aC)/λ → (1/aC) Σ_θ Σ_γ aC φ_γ p_{γ,1}(θ,1|ρ(1))
− (1/(1 − aC)) Σ_θ Σ_γ (1 − aC) φ_γ p_{γ,0}(θ,1|ρ(1))`. -/
theorem cr_limit {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ) (hM : M.Standing)
    (aC : ℝ) (haC0 : 0 < aC) (haC1 : aC < 1)
    (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt aC 1).IsSteady (lam n) (tau n) (s n)) :
    Tendsto (fun n => M.crEst (lam n) aC (s n) / lam n) atTop
      (𝓝 (1 / aC * ∑ θ, ∑ γ, aC * M.sys.φ γ * M.pE (γ, 1) (θ, 1) (M.rhoL 1)
        - 1 / (1 - aC) * ∑ θ, ∑ γ, (1 - aC) * M.sys.φ γ * M.pE (γ, 0) (θ, 1) (M.rhoL 1))) := by sorry

end TwoSidedExp.DemandLimit
