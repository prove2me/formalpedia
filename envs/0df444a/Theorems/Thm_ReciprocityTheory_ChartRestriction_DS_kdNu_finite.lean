-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_finite
-- name    : ReciprocityTheory.ChartRestriction.DS.kdNu_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:29.226102+00:00
-- url     : https://prove2.me/theorems/ba6d8f9a-7ba4-42ed-b877-6971ecdf1144
-- title:
--   DS: kd Nu finite
-- statement:
--   The DS construction uses the kd Nu finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L35-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_KDensC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {E X : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem ReciprocityTheory.ChartRestriction.DS.kdNu_finite {m : Measure X} [IsFiniteMeasure m] {f : E → X} {U : Set E} (hU : MeasurableSet U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsFiniteMeasure (kdNu m f U) := by sorry
