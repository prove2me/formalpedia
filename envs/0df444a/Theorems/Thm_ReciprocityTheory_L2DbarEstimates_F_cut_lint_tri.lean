-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_lint_tri
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_lint_tri
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:48.06702+00:00
-- url     : https://prove2.me/theorems/636a658e-6459-5483-a6cf-2905c225bd64
-- title:
--   F: cut lint tri
-- statement:
--   The F construction uses the cut lint tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L237-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L237-L243

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_lint_tri {M : Type*} [MeasurableSpace M] (μ : Measure M) (F G H : M → ℝ≥0∞)
    (hG : AEMeasurable G μ) (h : ∀ x, F x ≤ 2 * H x + 2 * G x) :
    ∫⁻ x, F x ∂μ ≤ 2 * ∫⁻ x, H x ∂μ + 2 * ∫⁻ x, G x ∂μ := by sorry
