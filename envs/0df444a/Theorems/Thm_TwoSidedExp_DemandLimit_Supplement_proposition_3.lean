-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_proposition_3
-- name    : TwoSidedExp.DemandLimit.Supplement.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:24:54.684463+00:00
-- url     : https://prove2.me/theorems/9a1b798e-b910-4f5b-a03a-f788e7540031
-- title:
--   Proposition 3 (supports Theorem 4) — scaled booking-rate limit (23)
-- statement:
--   Fix M satisfying the standing assumptions and a design (a_C,a_L) ∈ [0,1]². Let λ_n,τ_n > 0 with λ_n/τ_n → ∞, and evaluate booking rates at any sequence of the design's steady states. For every customer condition i and listing condition j,
--
--   $$\frac{Q_{ij}(\infty\mid a_C,a_L)}{\tau_n}\longrightarrow\sum_\theta\frac{\sum_\gamma\phi_{\gamma,i}g_{\gamma,i}(\theta,j)}{\sum_{i'=0,1}\sum_\gamma\phi_{\gamma,i'}g_{\gamma,i'}(\theta,j)}\rho(\theta,j)\nu(\theta).$$
--
--   All parameters apart from λ_n and τ_n are fixed. This is the scaled booking-rate limit (23), including the global-control, global-treatment, CR and LR boundary designs needed by Theorem 4.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - reading: The proof of Proposition 3 reduces endpoint designs by deleting zero-mass groups. → All (aC,aL) in [0,1]² are included, with their forced zero steady-state coordinates.; reason: This retains the domain needed by the global-control, global-treatment, CR and LR evaluations.
--   - encoding: s* is the steady state for each system. → Every sequence of states satisfying the published steady-state equation is quantified.; reason: The published existence and uniqueness results supply the states; none is chosen or defined by its target limit.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 20 (PDF 20), Proposition 3

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Proposition 3 (23), p. 20, on the closed design square. -/
theorem proposition_3 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop atTop)
    (aC aL : ℝ) (haC : 0 ≤ aC ∧ aC ≤ 1) (haL : 0 ≤ aL ∧ aL ≤ 1)
    (s : ℕ → Θ × Fin 2 → ℝ)
    (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ i j : Fin 2, Tendsto (fun n => M.Q (lam n) aC aL (s n) i j / tau n) atTop
      (𝓝 (∑ θ, ((∑ γ, (M.expt aC aL).φ (γ, i) * g M (γ, i) (θ, j)) /
        (∑ i' : Fin 2, ∑ γ, (M.expt aC aL).φ (γ, i') * g M (γ, i') (θ, j))) *
          (M.expt aC aL).ρ (θ, j) * M.sys.ν θ)) := by sorry

end TwoSidedExp.DemandLimit.Supplement
