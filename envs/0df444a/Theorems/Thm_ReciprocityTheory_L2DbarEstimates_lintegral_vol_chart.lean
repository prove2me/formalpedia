-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lintegral_vol_chart
-- name    : ReciprocityTheory.L2DbarEstimates.lintegral_vol_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:11.408988+00:00
-- url     : https://prove2.me/theorems/9ed2e4cf-461f-4213-8326-8979912af616
-- title:
--   L2 Dbar Estimates: lintegral vol chart
-- statement:
--   The L2 Dbar Estimates construction uses the lintegral vol chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L195-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L195-L205

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

theorem ReciprocityTheory.L2DbarEstimates.lintegral_vol_chart {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℝ≥0∞) (hf : Measurable f) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by sorry
