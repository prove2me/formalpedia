-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
-- name    : ReciprocityTheory.L2DbarEstimates.Smooth.continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:03.794799+00:00
-- url     : https://prove2.me/theorems/d4c85de4-4fef-4994-9a83-8567d2396f25
-- title:
--   Smooth: continuous
-- statement:
--   The Smooth construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L100-L109

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Smooth.continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Smooth n z f) : Continuous f := by sorry
