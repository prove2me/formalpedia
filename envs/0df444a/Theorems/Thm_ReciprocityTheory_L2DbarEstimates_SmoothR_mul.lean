-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
-- name    : ReciprocityTheory.L2DbarEstimates.SmoothR.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:15.157132+00:00
-- url     : https://prove2.me/theorems/d7587a7d-c2e9-44d4-a742-18f7b34c9ac1
-- title:
--   Smooth R: mul
-- statement:
--   The Smooth R construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L66-L70

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

theorem ReciprocityTheory.L2DbarEstimates.SmoothR.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ) (hf : SmoothR n z f) (hg : SmoothR n z g) :
    SmoothR n z (fun x => f x * g x) := by sorry
