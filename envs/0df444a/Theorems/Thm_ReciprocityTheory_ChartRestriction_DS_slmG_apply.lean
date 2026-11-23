-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.slmG_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:45.361109+00:00
-- url     : https://prove2.me/theorems/0a440e19-3aa2-4a3c-a9db-a274d4a69a88
-- title:
--   DS: slm G apply
-- statement:
--   The DS construction uses the slm G apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L94-L96

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

theorem ReciprocityTheory.ChartRestriction.DS.slmG_apply (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) :
    slmG C fd w W = ∑ i, (C i (fd W)) • w i := by sorry
