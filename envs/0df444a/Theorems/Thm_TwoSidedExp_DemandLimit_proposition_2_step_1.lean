-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_proposition_2_step_1
-- name    : TwoSidedExp.DemandLimit.proposition_2_step_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:33.091354+00:00
-- url     : https://prove2.me/theorems/efb50358-bca2-4b80-ac52-679a11b6f227
-- title:
--   Proposition 2, proof Step 1, p. A7 — as λ/τ → 0 the steady-state availability s∗(θ,j) tends to the full mass ρ(θ,j)
-- statement:
--   Fix all parameters of the model and a design $(a_C,a_L)\in[0,1]^2$, and let $(\lambda_n,\tau_n)$ be a sequence with $\lambda_n,\tau_n>0$ and $\lambda_n/\tau_n\to0$. Let $s_n$ be a steady state of the TSR experimental system for $(\lambda_n,\tau_n)$, for every $n$. Then for every listing type $\theta$ and treatment condition $j$,
--   $$s_n(\theta,j)\longrightarrow\rho(\theta,j)\qquad(n\to\infty),$$
--   where $\rho(\theta,1)=a_L\rho(\theta)$ and $\rho(\theta,0)=(1-a_L)\rho(\theta)$.
--
--   In a highly demand-constrained market almost every listing is available in steady state.
--
--   **Formalization Note** The steady states are quantified over (any sequence of them), not chosen. The design ranges over the closed square because Theorem 3 uses boundary designs.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, Proof of Proposition 2, Step 1, p. A7

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Proof of Proposition 2, Step 1, p. A7: along a sequence of systems with `λ/τ → 0`, the
steady-state availability `s*(θ,j)` of the design `(aC, aL)` tends to the mass `ρ(θ,j)`. -/
theorem proposition_2_step_1 {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (aC aL : ℝ) (haC : aC ∈ Set.Icc (0 : ℝ) 1) (haL : aL ∈ Set.Icc (0 : ℝ) 1)
    (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ θ j, Tendsto (fun n => s n (θ, j)) atTop (𝓝 ((M.expt aC aL).ρ (θ, j))) := by sorry

end TwoSidedExp.DemandLimit
