-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_contR
-- name    : ReciprocityTheory.L2DbarEstimates.F.multA_contR
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:40.029483+00:00
-- url     : https://prove2.me/theorems/00283798-8381-4ea1-9fbc-264579e003bb
-- title:
--   F: mult A cont R
-- statement:
--   The F construction uses the mult A cont R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L96-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L96-L109

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
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

theorem ReciprocityTheory.L2DbarEstimates.F.multA_contR {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by sorry
