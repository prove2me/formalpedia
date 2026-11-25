-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_TopClm_integral_ne_zero_of_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.TopClm.integral_ne_zero_of_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:53.752512+00:00
-- url     : https://prove2.me/theorems/b3e08d97-7258-5ad9-9f47-a35bb22d020c
-- title:
--   Top Clm: integral ne zero of apply
-- statement:
--   The Top Clm construction uses the integral ne zero of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/BesselVectors/ClmInt.lean#L15-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/BesselVectors/ClmInt.lean#L15-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_BesselVectors_ClmInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.TopClm.integral_ne_zero_of_apply (s : α → ℂ) (A : α → V →L[ℂ] V) (hA : AEStronglyMeasurable A μ)
    (hu : ∀ᵐ p ∂μ, ∀ v, ‖A p v‖ = ‖v‖) (ξ : V) (h : ∫ p, s p • A p ξ ∂μ ≠ 0) :
    ∫ p, s p • A p ∂μ ≠ 0 := by sorry
