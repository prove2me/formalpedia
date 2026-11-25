-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_gauss_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:15.822485+00:00
-- url     : https://prove2.me/theorems/a51e1890-74eb-57e1-8564-c10dca6d4f7a
-- title:
--   Laplace: gauss ne zero
-- statement:
--   The Laplace construction uses the gauss ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L171-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L171-L192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) : ∫ v, cexp (-(B v v)) ∂μ ≠ 0 := by sorry
