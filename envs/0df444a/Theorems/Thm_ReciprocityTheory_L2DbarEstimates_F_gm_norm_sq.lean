-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_norm_sq
-- name    : ReciprocityTheory.L2DbarEstimates.F.gm_norm_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:41:45.456516+00:00
-- url     : https://prove2.me/theorems/b303b8d7-edfd-4679-8dd8-cd02614e31fb
-- title:
--   F: gm norm sq
-- statement:
--   The F construction uses the gm norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L285-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L285-L290

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
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
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

theorem ReciprocityTheory.L2DbarEstimates.F.gm_norm_sq {E : Type*} [NormedAddCommGroup E] {μ : Measure M} (u : Lp E 2 μ) :
    ENNReal.ofReal (‖u‖ ^ 2) = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂μ := by sorry
