-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
-- name    : ReciprocityTheory.L2DbarEstimates.Smooth.conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:04.132455+00:00
-- url     : https://prove2.me/theorems/4aec2290-0cf4-4069-870f-b922f18302d1
-- title:
--   Smooth: conj
-- statement:
--   The Smooth construction uses the conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L26-L31

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

theorem ReciprocityTheory.L2DbarEstimates.Smooth.conj {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    Smooth n z (fun x => (starRingEnd ℂ) (f x)) := by sorry
