-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_theorem_1_step_5
-- name    : TwoSidedExp.DemandLimit.Supplement.theorem_1_step_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:19:51.361652+00:00
-- url     : https://prove2.me/theorems/e526ab91-3dd1-4f80-9503-f10e891d26f3
-- title:
--   Proof of Theorem 1, Step 5 (supports Theorem 1 (global asymptotic stability)) — Lyapunov identity, signs and convergence (corrected: shifted energy)
-- statement:
--   Let M satisfy the standing assumptions, let λ,τ > 0, and let s* be any steady state of its base mean-field system. For any trajectory s_t starting with s₀(θ) > 0, all coordinates stay positive. Put y_t = log s_t and y* = log s*. On Y = {y : y(θ) ≤ log ρ(θ)}, V is differentiable and ∂_θV(y) = −f_θ(e^y). For every t ≥ 0,
--
--   $$\frac{d}{dt}W(s_t)=-\sum_\theta\frac{(\partial_\theta V(y_t))^2}{s_t(\theta)}.$$
--
--   This derivative is negative exactly when s_t ≠ s*, and is zero exactly when s_t = s*. On all positive feasible states z, W(z) − W(s*) ≥ 0, with equality exactly at s*. Moreover,
--
--   $$y_t\longrightarrow y^*\quad(t\to\infty).$$
--
--   This is the Lyapunov statement used for positive starts in the stability argument.
--
--   **Formalization Note** The energy is shifted at the steady state: V itself need not be nonnegative or vanish there. This repairs the printed positive-definiteness sentence without changing derivatives or limits.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - encoding: The source uses trajectories on t ≥ 0. → Coordinate right derivatives at zero and derivatives on [0,∞) are used; uniqueness compares only nonnegative times.; reason: Negative-time extensions have no mathematical meaning for this initial-value problem.
--   - correction: Step 5 says V is positive definite. → W(z) − W(s*) is nonnegative and vanishes only at s*, while its derivative is strictly negative away from s*.; reason: The source has already shown that y* uniquely minimizes V; subtracting V(y*) supplies the missing normalization. V can be negative, for example with one type, α=1, v=ϵ=1/100, λ=τ=ρ=φ=ν=1. No initial states or parameter values are excluded.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. A2 (PDF 38), Proof of Theorem 1, Step 5

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Lyapunov

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Step 5, p. A2: actual derivatives, strict dissipation, shifted positivity and log convergence. -/
theorem theorem_1_step_5 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) (sstar : Θ → ℝ)
    (hstar : M.sys.IsSteady lam tau sstar) (s : ℝ → Θ → ℝ)
    (hs : Trajectory M.sys lam tau s) (hpos₀ : ∀ θ, 0 < s 0 θ) :
    (∀ t, 0 ≤ t → ∀ θ, 0 < s t θ) ∧
    (∀ y : Θ → ℝ, (∀ θ, y θ ≤ Real.log (M.sys.ρ θ)) →
      DifferentiableAt ℝ (V M.sys lam tau) y ∧
      ∀ θ, partialV M.sys lam tau y θ = -drift M.sys lam tau (fun θ => Real.exp (y θ)) θ) ∧
    (∀ t, 0 ≤ t →
      HasDerivWithinAt (fun u => M.sys.W lam tau (s u))
        (dissipation M.sys lam tau (s t)) (Set.Ici 0) t ∧
      (dissipation M.sys lam tau (s t) < 0 ↔ s t ≠ sstar) ∧
      (dissipation M.sys lam tau (s t) = 0 ↔ s t = sstar)) ∧
    (∀ z : Θ → ℝ, M.sys.InS z → (∀ θ, 0 < z θ) →
      0 ≤ M.sys.W lam tau z - M.sys.W lam tau sstar ∧
      (M.sys.W lam tau z - M.sys.W lam tau sstar = 0 ↔ z = sstar)) ∧
    Tendsto (fun t θ => Real.log (s t θ)) atTop (𝓝 (fun θ => Real.log (sstar θ))) := by sorry

end TwoSidedExp.DemandLimit.Supplement
