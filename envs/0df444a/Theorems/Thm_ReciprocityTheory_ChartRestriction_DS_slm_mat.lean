-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_mat
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:12.624186+00:00
-- url     : https://prove2.me/theorems/bfc2f033-d853-4e06-a202-195ec02af4be
-- title:
--   DS: slm mat
-- statement:
--   The DS construction uses the slm mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L278-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L278-L291

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.slm_mat {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hm : ContDiffOn ℝ ∞ m V) (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hP : ∀ F, P F → ∀ a b, P (Op a b F))
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) :
    ∀ F, P F → ContDiffOn ℝ ∞ (Φ F) V := by sorry
