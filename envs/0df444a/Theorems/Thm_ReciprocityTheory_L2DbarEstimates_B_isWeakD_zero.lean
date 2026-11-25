-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_isWeakD_zero
-- name    : ReciprocityTheory.L2DbarEstimates.B.isWeakD_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:43.252244+00:00
-- url     : https://prove2.me/theorems/2af9ee6d-5124-42db-8a60-957831dc2e6f
-- title:
--   B: is Weak D zero
-- statement:
--   The B construction uses the is Weak D zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollifierL2LocTendsto.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollifierL2LocTendsto.lean#L129-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem ReciprocityTheory.L2DbarEstimates.B.isWeakD_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ) (c : Fin m → ℂ) (v : Fin m → E) :
    IsWeakD μ c v (fun _ => 0) 0 := by sorry
