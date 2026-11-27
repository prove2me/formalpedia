-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_proposition_3_step_1
-- name    : TwoSidedExp.DemandLimit.Supplement.proposition_3_step_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:23:50.262195+00:00
-- url     : https://prove2.me/theorems/08c1c018-d5ba-4f7e-aa66-324da6c1def6
-- title:
--   Proposition 3, proof Step 1 (supports Theorem 4) — availability tends to zero
-- statement:
--   Fix M satisfying the standing assumptions and a design (a_C,a_L) ∈ [0,1]². Along any positive sequence λ_n,τ_n with λ_n/τ_n → ∞, every sequence of experimental steady states satisfies, for each θ and j,
--
--   $$s_n^*(\theta,j)\longrightarrow0.$$
--
--   This is Step 1 of Proposition 3's proof: availability vanishes in the supply-constrained limit. Zero-mass groups are included.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - reading: The proof of Proposition 3 reduces endpoint designs by deleting zero-mass groups. → All (aC,aL) in [0,1]² are included, with their forced zero steady-state coordinates.; reason: This retains the domain needed by the global-control, global-treatment, CR and LR evaluations.
--   - encoding: s* is the steady state for each system. → Every sequence of states satisfying the published steady-state equation is quantified.; reason: The published existence and uniqueness results supply the states; none is chosen or defined by its target limit.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. A8 (PDF 44), Proposition 3, proof Step 1

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Proposition 3 Step 1, p. A8, on the closed design square. -/
theorem proposition_3_step_1 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop atTop)
    (aC aL : ℝ) (haC : 0 ≤ aC ∧ aC ≤ 1) (haL : 0 ≤ aL ∧ aL ≤ 1)
    (s : ℕ → Θ × Fin 2 → ℝ)
    (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ p : Θ × Fin 2, Tendsto (fun n => s n p) atTop (𝓝 0) := by sorry

end TwoSidedExp.DemandLimit.Supplement
