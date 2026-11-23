-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
-- name    : ReciprocityTheory.L2DbarEstimates.Smooth.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:22.275538+00:00
-- url     : https://prove2.me/theorems/9e895acc-4e93-4ff5-b75e-f0548b6c816e
-- title:
--   Smooth: sub
-- statement:
--   The Smooth construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L18-L20

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

theorem ReciprocityTheory.L2DbarEstimates.Smooth.sub {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Smooth n z f) (hg : Smooth n z g) :
    Smooth n z (fun x => f x - g x) := by sorry
