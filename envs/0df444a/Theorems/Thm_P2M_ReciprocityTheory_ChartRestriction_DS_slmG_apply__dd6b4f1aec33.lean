-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_slmG_apply__dd6b4f1aec33
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_slmG_apply__dd6b4f1aec33
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:39.833689+00:00
-- url     : https://prove2.me/theorems/1f450193-f88d-4788-b396-7e68535bef78
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS slm G apply  dd6b4f1aec33: P2 M Reciprocity Theory Chart Restriction DS slm G apply  dd6b4f1aec33
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS slm G apply  dd6b4f1aec33 construction uses the P2 M Reciprocity Theory Chart Restriction DS slm G apply  dd6b4f1aec33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L98-L101

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_slmG_apply__dd6b4f1aec33 (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) (κ : ι → ℝ)
    (hκ : ∀ i, C i (fd W) = κ i) : slmG C fd w W = ∑ i, κ i • w i := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«slmG_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_slmG_apply__dd6b4f1aec33
