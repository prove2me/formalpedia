-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_coeFn_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.slm_coeFn_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:39.615726+00:00
-- url     : https://prove2.me/theorems/f2902dcd-2537-4aa2-acb8-2d3d7914ad47
-- title:
--   DS: slm coe Fn sum
-- statement:
--   The DS construction uses the slm coe Fn sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L299-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean#L299-L309

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
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ReciprocityTheory.ChartRestriction.DS.slm_coeFn_sum {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by sorry
