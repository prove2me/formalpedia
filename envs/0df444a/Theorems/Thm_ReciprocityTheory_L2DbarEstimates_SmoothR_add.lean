-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
-- name    : ReciprocityTheory.L2DbarEstimates.SmoothR.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:25.981076+00:00
-- url     : https://prove2.me/theorems/39ee80ed-1c0b-4cf1-92a3-45fe02d8ca78
-- title:
--   Smooth R: add
-- statement:
--   The Smooth R construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L60-L64

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.SmoothR.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ) (hf : SmoothR n z f) (hg : SmoothR n z g) :
    SmoothR n z (fun x => f x + g x) := by sorry
