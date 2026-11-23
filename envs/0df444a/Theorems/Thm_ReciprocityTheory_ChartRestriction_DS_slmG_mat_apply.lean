-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_mat_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.slmG_mat_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:02.326981+00:00
-- url     : https://prove2.me/theorems/9f69bff9-b4ad-417b-bcff-eab7a4e1c1b9
-- title:
--   DS: slm G mat apply
-- statement:
--   The DS construction uses the slm G mat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L223-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L223-L236

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

theorem ReciprocityTheory.ChartRestriction.DS.slmG_mat_apply (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (q : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → Fin n → E) (W : Matrix (Fin n) (Fin n) ℂ) :
    slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • v i.1 i.2.1) W =
      ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • v a b := by sorry
