-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_of_le_sum
-- name    : ReciprocityTheory.L2DbarEstimates.F.locL2_of_le_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:16.675446+00:00
-- url     : https://prove2.me/theorems/85b917f1-c04a-5fa3-8464-f64171fc3c6b
-- title:
--   F: loc L2 of le sum
-- statement:
--   The F construction uses the loc L2 of le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L156-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L156-L168

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.locL2_of_le_sum {M E F₁ F₂ : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] (μ : Measure M)
    (f : M → E) (g₁ : M → F₁) (g₂ : M → F₂) (c : ℝ) (h₁ : LocalL2Isometry μ g₁) (h₂ : LocalL2Isometry μ g₂)
    (hf : AEStronglyMeasurable f μ) (hle : ∀ x, ‖f x‖ ≤ c * (‖g₁ x‖ + ‖g₂ x‖)) : LocalL2Isometry μ f := by sorry
