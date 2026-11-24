-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_theorem_4
-- name    : TwoSidedExp.DemandLimit.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:25:29.779858+00:00
-- url     : https://prove2.me/theorems/f30b8f97-d238-43d9-9e6d-b6487766de2a
-- title:
--   Theorem 4 (companion theorem; not used in the proof of the goal) — supply-constrained GTE, LR and generic CR limits
-- statement:
--   Fix M satisfying the standing assumptions. Along every sequence λ_n,τ_n > 0 with λ_n/τ_n → ∞, with rates evaluated at the respective experimental steady states,
--
--   $$\mathrm{GTE}/\tau_n\longrightarrow0,$$
--   $$\widehat{\mathrm{GTE}}^{\mathrm{LR}}(\infty\mid a_L)/\tau_n\longrightarrow0\qquad(0<a_L<1).$$
--
--   For every a_C ∈ (0,1), for Lebesgue-almost every positive treatment-utility array w, there is a real number L ≠ 0 such that, along every such sequence and every choice of its CR, global-treatment and global-control steady states,
--
--   $$\widehat{\mathrm{GTE}}^{\mathrm{CR}}(\infty\mid a_C)/\tau_n-\mathrm{GTE}/\tau_n\longrightarrow L.$$
--
--   The utilities in both estimators and the GTE are replaced by that same w; all other parameters stay fixed. This is the supply-constrained companion to the published demand-constrained goal, with all three conclusions retained.
--
--   **Formalization Note** Genericity uses the same fiberwise Lebesgue-almost-everywhere reading as the published goal. The nonzero L is chosen before the system sequences and states. The listing-side conclusion is the limit of the estimator itself, as printed.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - encoding: s* is the steady state for each system. → Every sequence of states satisfying the published steady-state equation is quantified.; reason: The published existence and uniqueness results supply the states; none is chosen or defined by its target limit.
--   - reading: Generic parameter values exclude a Lebesgue-null set (footnote 7). → For each choice of the other parameters and each aC in (0,1), almost every positive treatment-utility array has one nonzero limit along all sequences and steady states.; reason: This uses the same fiberwise reading as the published goal; taking ambient Lebesgue measure on the mass simplices would be vacuous.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 22 (PDF 22), Theorem 4

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Theorem 4, p. 22, including all three clauses and the generic limit's quantifier order. -/
theorem theorem_4 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) :
    (∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
      Tendsto (fun n => lam n / tau n) atTop atTop →
      ∀ (sGT sGC : ℕ → Θ × Fin 2 → ℝ),
        (∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
        (∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
      Tendsto (fun n => M.gte (lam n) (sGT n) (sGC n) / tau n) atTop (𝓝 0)) ∧
    (∀ aL : ℝ, 0 < aL → aL < 1 →
      ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
        Tendsto (fun n => lam n / tau n) atTop atTop →
      ∀ sLR : ℕ → Θ × Fin 2 → ℝ,
        (∀ n, (M.expt 1 aL).IsSteady (lam n) (tau n) (sLR n)) →
      Tendsto (fun n => M.lrEst (lam n) aL (sLR n) / tau n) atTop (𝓝 0)) ∧
    (∀ aC : ℝ, 0 < aC → aC < 1 →
      ∀ᵐ w ∂(volume : Measure (Γ → Θ → ℝ)), (∀ γ θ, 0 < w γ θ) →
        ∃ L : ℝ, L ≠ 0 ∧
          ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
            Tendsto (fun n => lam n / tau n) atTop atTop →
          ∀ (sCR sGT sGC : ℕ → Θ × Fin 2 → ℝ),
            (∀ n, ((M.withVt w).expt aC 1).IsSteady (lam n) (tau n) (sCR n)) →
            (∀ n, ((M.withVt w).expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
            (∀ n, ((M.withVt w).expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
          Tendsto (fun n => (M.withVt w).crEst (lam n) aC (sCR n) / tau n
            - (M.withVt w).gte (lam n) (sGT n) (sGC n) / tau n) atTop (𝓝 L)) := by sorry

end TwoSidedExp.DemandLimit.Supplement
