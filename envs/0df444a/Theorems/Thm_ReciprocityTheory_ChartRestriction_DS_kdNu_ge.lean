-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_ge
-- name    : ReciprocityTheory.ChartRestriction.DS.kdNu_ge
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:37.607366+00:00
-- url     : https://prove2.me/theorems/3a336a4b-b1e2-4c4f-98aa-a76ffa809e1e
-- title:
--   DS: kd Nu ge
-- statement:
--   The DS construction uses the kd Nu ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/KDensC.lean#L46-L51

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

theorem ReciprocityTheory.ChartRestriction.DS.kdNu_ge {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (d : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → d * lam A ≤ m (f '' A)) : d • lam.restrict U ≤ kdNu m f U := by sorry
