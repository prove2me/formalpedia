-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_eq_46
-- name    : TwoSidedExp.DemandLimit.eq_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:35.015319+00:00
-- url     : https://prove2.me/theorems/efb27fc5-257c-4f36-a46e-edc90afda1ad
-- title:
--   (46), proof of Theorem 3, p. A7 — the scaled global treatment effect GTE/λ converges as λ/τ → 0
-- statement:
--   Let $\lambda_n,\tau_n>0$ with $\lambda_n/\tau_n\to0$, and let $s^{GT}_n$ and $s^{GC}_n$ be steady states of the global-treatment design $(1,1)$ and the global-control design $(0,0)$. With $\mathrm{GTE}_n=Q_{11}(\infty\mid1,1)-Q_{00}(\infty\mid0,0)$ evaluated at these states,
--   $$\frac{1}{\lambda_n}\mathrm{GTE}_n\longrightarrow\sum_\theta\sum_\gamma\phi_\gamma\,p_{\gamma,1}(\theta,1\mid\rho(1))-\sum_\theta\sum_\gamma\phi_\gamma\,p_{\gamma,0}(\theta,0\mid\rho(0)).$$
--   Here $\rho(1)$ is the mass vector with every listing treated and $\rho(0)$ the one with every listing in control.
--
--   This is the benchmark against which both naive estimators are compared in Theorem 3.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, Proof of Theorem 3, p. A7, (46)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- (46), proof of Theorem 3, p. A7: along a sequence of systems with `λ/τ → 0`,
`GTE/λ → Σ_θ Σ_γ φ_γ p_{γ,1}(θ,1|ρ(1)) − Σ_θ Σ_γ φ_γ p_{γ,0}(θ,0|ρ(0))`. -/
theorem eq_46 {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ) (hM : M.Standing)
    (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (sGT sGC : ℕ → Θ × Fin 2 → ℝ)
    (hGT : ∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n))
    (hGC : ∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) :
    Tendsto (fun n => M.gte (lam n) (sGT n) (sGC n) / lam n) atTop
      (𝓝 (∑ θ, ∑ γ, M.sys.φ γ * M.pE (γ, 1) (θ, 1) (M.rhoL 1)
        - ∑ θ, ∑ γ, M.sys.φ γ * M.pE (γ, 0) (θ, 0) (M.rhoL 0))) := by sorry

end TwoSidedExp.DemandLimit
