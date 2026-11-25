-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_of_weighted_bound
-- name    : ReciprocityTheory.L2DbarEstimates.F.locL2_of_weighted_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:12.364949+00:00
-- url     : https://prove2.me/theorems/74aec0c3-4866-4114-bfcf-6a62621a4a4f
-- title:
--   F: loc L2 of weighted bound
-- statement:
--   The F construction uses the loc L2 of weighted bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L194-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L194-L235

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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

theorem ReciprocityTheory.L2DbarEstimates.F.locL2_of_weighted_bound {M E : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] [NormedAddCommGroup E]
    (μ : Measure M) (u : M → E) (q ph : M → ℝ) (c : ℝ) (hc : 0 ≤ c) (hph : Continuous ph)
    (hu : AEStronglyMeasurable u μ) (hq : ∀ x, ‖u x‖ ^ 2 ≤ c * q x)
    (h : ∫⁻ x, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ < ⊤) : LocalL2Isometry μ u := by sorry
