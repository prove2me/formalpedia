-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_contDiffOn_zero_of_continuousOn
-- name    : ReciprocityTheory.ChartRestriction.DS.contDiffOn_zero_of_continuousOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:26.348212+00:00
-- url     : https://prove2.me/theorems/fe3a65db-5c28-4e65-936c-385192652ceb
-- title:
--   DS: cont Diff On zero of continuous On
-- statement:
--   The DS construction uses the cont Diff On zero of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L114-L118

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

theorem ReciprocityTheory.ChartRestriction.DS.contDiffOn_zero_of_continuousOn {V : Set X} {f : X → E} (h : ContinuousOn f V) : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) f V := by sorry
