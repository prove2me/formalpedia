-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_cd
-- name    : ReciprocityTheory.ChartRestriction.DS.slmG_cd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:45.284718+00:00
-- url     : https://prove2.me/theorems/ef978efa-952b-4e7b-81df-b82fda61a40b
-- title:
--   DS: slm G cd
-- statement:
--   The DS construction uses the slm G cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L103-L112

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
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.DS.slmG_cd {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {N : ℕ} {w : ι → X → E} (hw : ∀ i, ContDiffOn ℝ N (w i) V) :
    ContDiffOn ℝ N (fun q => slmG C (fderiv ℝ γ q) (fun i => w i q)) V := by sorry
