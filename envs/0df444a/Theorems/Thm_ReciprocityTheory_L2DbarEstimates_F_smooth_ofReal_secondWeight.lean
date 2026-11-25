-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_smooth_ofReal_secondWeight
-- name    : ReciprocityTheory.L2DbarEstimates.F.smooth_ofReal_secondWeight
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:15.482343+00:00
-- url     : https://prove2.me/theorems/9e035ccf-1f8c-5691-a11f-1f50ea820bf4
-- title:
--   F: smooth of Real second Weight
-- statement:
--   The F construction uses the smooth of Real second Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L183-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L183-L190

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
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

theorem ReciprocityTheory.L2DbarEstimates.F.smooth_ofReal_secondWeight {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ : M → ℝ)
    (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    Smooth n z (fun y => ((w2 ph ψ y : ℝ) : ℂ)) := by sorry
