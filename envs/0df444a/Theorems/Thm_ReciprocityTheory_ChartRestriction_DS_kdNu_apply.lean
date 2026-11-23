-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.kdNu_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:37.676171+00:00
-- url     : https://prove2.me/theorems/88f6a1ca-ae11-4245-ba6b-5431cf6159e1
-- title:
--   DS: kd Nu apply
-- statement:
--   The DS construction uses the kd Nu apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L18-L33

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

theorem ReciprocityTheory.ChartRestriction.DS.kdNu_apply {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) {A : Set E} (hA : MeasurableSet A) : kdNu m f U A = m (f '' (A ∩ U)) := by sorry
