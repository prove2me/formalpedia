-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_lintegral_sum_lt
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_lintegral_sum_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:52.074928+00:00
-- url     : https://prove2.me/theorems/05a0f1e9-08b6-44fd-9acc-b5f4bc4c6f4c
-- title:
--   F: loc lintegral sum lt
-- statement:
--   The F construction uses the loc lintegral sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L504-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L504-L517

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

theorem ReciprocityTheory.L2DbarEstimates.F.loc_lintegral_sum_lt {M : Type*} [MeasurableSpace M] (μ : Measure M) {N : ℕ}
    (F : M → ℝ≥0∞) (f : Fin N → M → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ)
    (hle : ∀ x, F x ≤ N * ∑ i, f i x) (δ' δ : ℝ≥0∞) (hi : ∀ i, ∫⁻ x, f i x ∂μ < δ')
    (hδ : δ' * (N * N) < δ) : ∫⁻ x, F x ∂μ < δ := by sorry
