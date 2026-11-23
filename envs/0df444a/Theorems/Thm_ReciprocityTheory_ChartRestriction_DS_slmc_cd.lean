-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmc_cd
-- name    : ReciprocityTheory.ChartRestriction.DS.slmc_cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:08.848882+00:00
-- url     : https://prove2.me/theorems/561cc563-a42d-42e0-9d2e-3639016a31e7
-- title:
--   DS: slmc cd
-- statement:
--   The DS construction uses the slmc cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L212-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L212-L219

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

theorem ReciprocityTheory.ChartRestriction.DS.slmc_cd {V : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hm : ContDiffOn ℝ ∞ m V) (i : Fin n × Fin n × Fin n × Bool) : ContDiffOn ℝ ∞ (slmc m i) V := by sorry
