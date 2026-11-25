-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_aemeasurable_unweighted_two_form
-- name    : ReciprocityTheory.L2DbarEstimates.F.aemeasurable_unweighted_two_form
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:02:10.876624+00:00
-- url     : https://prove2.me/theorems/84f3dc49-0189-48db-a113-9c6be13166e0
-- title:
--   F: aemeasurable unweighted two form
-- statement:
--   The F construction uses the aemeasurable unweighted two form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L525-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L525-L529

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.aemeasurable_unweighted_two_form {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M)
    (σ : M → Fin n → Fin n → ℂ) (h : AEStronglyMeasurable σ μ) :
    AEMeasurable (fun x => ENNReal.ofReal (sq2 n (σ x) * Real.exp (-(fun _ : M => (0 : ℝ)) x))) μ := by sorry
