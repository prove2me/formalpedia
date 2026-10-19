-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_proposition_2
-- name    : TwoSidedExp.DemandLimit.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:40.723509+00:00
-- url     : https://prove2.me/theorems/ac143438-e4c1-4ba6-9c47-7b432e4eda2f
-- title:
--   Proposition 2, p. 19 — as λ/τ → 0, Qij(∞|aC,aL)/λ tends to the booking rate with every listing available
-- statement:
--   Fix all parameters of the model and a design $(a_C,a_L)\in[0,1]^2$, and let $\lambda_n,\tau_n>0$ with $\lambda_n/\tau_n\to0$. Let $s_n$ be a steady state of the TSR experimental system for $(\lambda_n,\tau_n)$. Then for all $i,j\in\{0,1\}$,
--   $$\frac{1}{\lambda_n}Q_{ij}(\infty\mid a_C,a_L)\longrightarrow\sum_\theta\sum_\gamma\phi_{\gamma,i}\,p_{\gamma,i}(\theta,j\mid\rho),$$
--   where $Q_{ij}$ is evaluated at $s_n$, $\phi_{\gamma,1}=a_C\phi_\gamma$, $\phi_{\gamma,0}=(1-a_C)\phi_\gamma$, and $\rho=\rho(a_L)$ is the vector of experimental masses $\rho(\theta,1)=a_L\rho(\theta)$, $\rho(\theta,0)=(1-a_L)\rho(\theta)$.
--
--   In the demand-constrained limit, the scaled booking rates behave as if every listing were available.
--
--   **Formalization Note** $Q_{ij}(\infty)$ is the right side of (18) at the steady state $s_n$. The paper's proof assumes $0<a_C,a_L<1$ "without loss of generality"; since Theorem 3 uses the proposition at $(1,1)$, $(0,0)$, $(a_C,1)$, $(1,a_L)$, it is stated on the closed square.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 19, Proposition 2, (22)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Proposition 2, p. 19, (22): along a sequence of systems with `λ/τ → 0`,
`Q_ij(∞|aC,aL)/λ → Σ_θ Σ_γ φ_{γ,i} p_{γ,i}(θ,j|ρ)`, for every design `(aC, aL) ∈ [0,1]²`. -/
theorem proposition_2 {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (aC aL : ℝ) (haC : aC ∈ Set.Icc (0 : ℝ) 1) (haL : aL ∈ Set.Icc (0 : ℝ) 1)
    (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ i j : Fin 2, Tendsto (fun n => M.Q (lam n) aC aL (s n) i j / lam n) atTop
      (𝓝 (∑ θ, ∑ γ, (M.expt aC aL).φ (γ, i) *
        (M.expt aC aL).choice (γ, i) (θ, j) (M.expt aC aL).ρ)) := by sorry

end TwoSidedExp.DemandLimit
