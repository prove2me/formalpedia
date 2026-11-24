-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_proposition_3_step_2
-- name    : TwoSidedExp.DemandLimit.Supplement.proposition_3_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:24:23.46118+00:00
-- url     : https://prove2.me/theorems/f463db64-82f8-422f-b9ec-1973e2f46d45
-- title:
--   Proposition 3, proof Step 2 (supports Theorem 4) — first-order availability expansion
-- statement:
--   Fix M satisfying the standing assumptions and a design (a_C,a_L) ∈ [0,1]². Let g be the supply-constrained choice weight and let λ_n,τ_n > 0 with λ_n/τ_n → ∞. For every sequence of experimental steady states and each θ,j,
--
--   $$\frac{\lambda_n}{\tau_n}s_n^*(\theta,j)\longrightarrow\frac{\rho(\theta,j)\nu(\theta)}{\sum_\gamma\sum_{i=0,1}\phi_{\gamma,i}g_{\gamma,i}(\theta,j)}.$$
--
--   The denominator is positive for all designs in the closed square. The numerator is zero for zero-mass listing groups. This is the first-order expansion of availability used in the booking-rate limit.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - reading: The proof of Proposition 3 reduces endpoint designs by deleting zero-mass groups. → All (aC,aL) in [0,1]² are included, with their forced zero steady-state coordinates.; reason: This retains the domain needed by the global-control, global-treatment, CR and LR evaluations.
--   - encoding: s* is the steady state for each system. → Every sequence of states satisfying the published steady-state equation is quantified.; reason: The published existence and uniqueness results supply the states; none is chosen or defined by its target limit.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. A8 (PDF 44), Proposition 3, proof Step 2

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Proposition 3 Step 2, p. A8; no division by a zero-mass state. -/
theorem proposition_3_step_2 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop atTop)
    (aC aL : ℝ) (haC : 0 ≤ aC ∧ aC ≤ 1) (haL : 0 ≤ aL ∧ aL ≤ 1)
    (s : ℕ → Θ × Fin 2 → ℝ)
    (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ p : Θ × Fin 2, Tendsto (fun n => (lam n / tau n) * s n p) atTop
      (𝓝 ((M.expt aC aL).ρ p * M.sys.ν p.1 /
        (∑ γ, ∑ i : Fin 2, (M.expt aC aL).φ (γ, i) * g M (γ, i) p))) := by sorry

end TwoSidedExp.DemandLimit.Supplement
