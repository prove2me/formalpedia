-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_theorem_1_gas
-- name    : TwoSidedExp.DemandLimit.Supplement.theorem_1_gas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:20:24.875637+00:00
-- url     : https://prove2.me/theorems/ad200da4-2878-4c2a-af80-c70c27096751
-- title:
--   Theorem 1 (global asymptotic stability) (companion theorem; not used in the proof of the goal) — convergence from every feasible initial state
-- statement:
--   Let M satisfy the standing assumptions, λ,τ > 0, and let s* solve the published steady-state equation (9). Every trajectory of (8) with initial state in S satisfies
--
--   $$s_t\longrightarrow s^*\quad(t\to\infty).$$
--
--   Zero initial coordinates are allowed. This is the stability sentence of Theorem 1, complementing its already-published steady-state and optimization parts.
--
--   **Formalization Note** “Globally asymptotically stable” is stated in the source's explicit sense, namely convergence of all trajectories. The steady state is quantified rather than selected, and the trajectory predicate includes staying in S as in Proposition 1.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - encoding: The source uses trajectories on t ≥ 0. → Coordinate right derivatives at zero and derivatives on [0,∞) are used; uniqueness compares only nonnegative times.; reason: Negative-time extensions have no mathematical meaning for this initial-value problem.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 12 (PDF 12), Theorem 1 (global asymptotic stability)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- The stability sentence of Theorem 1, p. 12, including boundary initial conditions. -/
theorem theorem_1_gas {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) (sstar : Θ → ℝ)
    (hstar : M.sys.IsSteady lam tau sstar) (s : ℝ → Θ → ℝ)
    (hs : Trajectory M.sys lam tau s) :
    Tendsto s atTop (𝓝 sstar) := by sorry

end TwoSidedExp.DemandLimit.Supplement
