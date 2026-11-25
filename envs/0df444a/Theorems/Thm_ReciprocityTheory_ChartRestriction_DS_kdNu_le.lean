-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_le
-- name    : ReciprocityTheory.ChartRestriction.DS.kdNu_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:33.217181+00:00
-- url     : https://prove2.me/theorems/55f38529-85f2-4cfd-b781-b6b2cf70e6a5
-- title:
--   DS: kd Nu le
-- statement:
--   The DS construction uses the kd Nu le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L39-L44

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

theorem ReciprocityTheory.ChartRestriction.DS.kdNu_le {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (c : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → m (f '' A) ≤ c * lam A) : kdNu m f U ≤ c • lam.restrict U := by sorry
