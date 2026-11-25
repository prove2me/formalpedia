-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_aem
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_aem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:31.661284+00:00
-- url     : https://prove2.me/theorems/99df4c1b-0a83-4734-92c9-4010081f79dc
-- title:
--   F: cut aem
-- statement:
--   The F construction uses the cut aem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L347-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L347-L353

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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_aem {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [NormedAddCommGroup E] (μ : Measure M) (u : M → E)
    (hu : AEStronglyMeasurable u μ) (ph : M → ℝ) (hph : Continuous ph) :
    AEMeasurable (fun x => ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x))) μ := by sorry
