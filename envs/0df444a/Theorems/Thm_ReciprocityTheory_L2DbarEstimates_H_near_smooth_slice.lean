-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_smooth_slice
-- name    : ReciprocityTheory.L2DbarEstimates.H.near_smooth_slice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:30.680191+00:00
-- url     : https://prove2.me/theorems/924eee0c-5616-4c3f-a68c-97b3aef22e34
-- title:
--   H: near smooth slice
-- statement:
--   The H construction uses the near smooth slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NearContinuousOfSmoothR.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NearContinuousOfSmoothR.lean#L59-L78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.H.near_smooth_slice {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (hN : ∀ x, gv g x ≠ 0) (u : M → ℂ) (hu : Holo n z u) (i : Fin p) :
    Smooth n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) := by sorry
