-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_proposition_1
-- name    : TwoSidedExp.DemandLimit.Supplement.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:21:18.76757+00:00
-- url     : https://prove2.me/theorems/e1a6d168-74ab-4a07-9db5-539c041207f0
-- title:
--   Proposition 1 (supports Theorem 2) — existence and uniqueness of the ODE trajectory
-- statement:
--   Let M satisfy the standing assumptions and let λ,τ > 0. For every initial vector ŝ with 0 ≤ ŝ(θ) ≤ ρ(θ), there is a solution of (8) on nonnegative times, and it is unique among solutions remaining in S:
--
--   $$s_0=\hat s,\qquad s_t\in S\ (t\ge0),\qquad \dot s_t=f(s_t).$$
--
--   Uniqueness means that any other such solution agrees at every nonnegative time. This supplies the trajectory in Theorem 2 and ensures that boundary initial conditions belong to the dynamical model.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - encoding: The source uses trajectories on t ≥ 0. → Coordinate right derivatives at zero and derivatives on [0,∞) are used; uniqueness compares only nonnegative times.; reason: Negative-time extensions have no mathematical meaning for this initial-value problem.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 11 (PDF 11), Proposition 1

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Proposition 1, p. 11: existence and uniqueness on nonnegative times. -/
theorem proposition_1 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) (s₀ : Θ → ℝ) (hs₀ : M.sys.InS s₀) :
    ∃ s : ℝ → Θ → ℝ, Trajectory M.sys lam tau s ∧ s 0 = s₀ ∧
      ∀ z : ℝ → Θ → ℝ, Trajectory M.sys lam tau z → z 0 = s₀ →
        ∀ t, 0 ≤ t → z t = s t := by sorry

end TwoSidedExp.DemandLimit.Supplement
