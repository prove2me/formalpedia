-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_vol_chart
-- name    : ReciprocityTheory.L2DbarEstimates.integral_vol_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:56.832908+00:00
-- url     : https://prove2.me/theorems/28daf7b6-eed8-4b80-aec2-725118bea304
-- title:
--   L2 Dbar Estimates: integral vol chart
-- statement:
--   The L2 Dbar Estimates construction uses the integral vol chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L207-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L207-L218

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.integral_vol_chart {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℂ) (hf : Measurable f) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫ x, f x ∂vol n z = ∫ y in e.target, f (e.symm y) := by sorry
