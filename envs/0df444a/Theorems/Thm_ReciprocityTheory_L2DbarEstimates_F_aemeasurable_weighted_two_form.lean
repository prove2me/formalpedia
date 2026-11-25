-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_aemeasurable_weighted_two_form
-- name    : ReciprocityTheory.L2DbarEstimates.F.aemeasurable_weighted_two_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:20.226124+00:00
-- url     : https://prove2.me/theorems/98e91e8f-5bb0-4d0f-90d2-ea1fabbb050e
-- title:
--   F: aemeasurable weighted two form
-- statement:
--   The F construction uses the aemeasurable weighted two form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L355-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L355-L362

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

theorem ReciprocityTheory.L2DbarEstimates.F.aemeasurable_weighted_two_form {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (μ : Measure M) (u : M → Fin n → Fin n → ℂ)
    (hu : AEStronglyMeasurable u μ) (ph : M → ℝ) (hph : Continuous ph) :
    AEMeasurable (fun x => ENNReal.ofReal (sq2 n (u x) * Real.exp (-ph x))) μ := by sorry
