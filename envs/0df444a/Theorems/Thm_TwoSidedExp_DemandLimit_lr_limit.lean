-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_lr_limit
-- name    : TwoSidedExp.DemandLimit.lr_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:37.862331+00:00
-- url     : https://prove2.me/theorems/3264ff18-68b7-4466-8504-84efe7aea3fd
-- title:
--   Proof of Theorem 3, p. A7 — limit of the scaled naive LR estimator ĜTE^LR(∞|aL)/λ as λ/τ → 0
-- statement:
--   Let $0<a_L<1$, let $\lambda_n,\tau_n>0$ with $\lambda_n/\tau_n\to0$, and let $s_n$ be a steady state of the listing-randomized design $(1,a_L)$. Then the steady-state naive LR estimator, evaluated at $s_n$, satisfies
--   $$\frac{1}{\lambda_n}\widehat{\mathrm{GTE}}^{\mathrm{LR}}(\infty\mid a_L)\longrightarrow\frac{1}{a_L}\sum_\theta\sum_\gamma\phi_\gamma\,p_{\gamma,1}(\theta,1\mid\rho(a_L))-\frac{1}{1-a_L}\sum_\theta\sum_\gamma\phi_\gamma\,p_{\gamma,1}(\theta,0\mid\rho(a_L)).$$
--
--   Because $\rho(a_L)$ differs from both $\rho(1)$ and $\rho(0)$, this limit differs from the GTE limit (46) in general: the source of the LR bias.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, Proof of Theorem 3, p. A7, LR display

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Proof of Theorem 3, p. A7, LR display: for `0 < aL < 1`, along a sequence of systems with
`λ/τ → 0`, `ĜTE^LR(∞|aL)/λ → (1/aL) Σ_θ Σ_γ φ_γ p_{γ,1}(θ,1|ρ(aL))
− (1/(1 − aL)) Σ_θ Σ_γ φ_γ p_{γ,1}(θ,0|ρ(aL))`. -/
theorem lr_limit {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ) (hM : M.Standing)
    (aL : ℝ) (haL0 : 0 < aL) (haL1 : aL < 1)
    (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt 1 aL).IsSteady (lam n) (tau n) (s n)) :
    Tendsto (fun n => M.lrEst (lam n) aL (s n) / lam n) atTop
      (𝓝 (1 / aL * ∑ θ, ∑ γ, M.sys.φ γ * M.pE (γ, 1) (θ, 1) (M.rhoL aL)
        - 1 / (1 - aL) * ∑ θ, ∑ γ, M.sys.φ γ * M.pE (γ, 1) (θ, 0) (M.rhoL aL))) := by sorry

end TwoSidedExp.DemandLimit
