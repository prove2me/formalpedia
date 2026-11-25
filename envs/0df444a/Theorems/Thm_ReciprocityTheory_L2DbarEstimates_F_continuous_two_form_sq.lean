-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_continuous_two_form_sq
-- name    : ReciprocityTheory.L2DbarEstimates.F.continuous_two_form_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:22.187934+00:00
-- url     : https://prove2.me/theorems/4ce693a4-12c9-5507-bf7c-e0d3255a50d8
-- title:
--   F: continuous two form sq
-- statement:
--   The F construction uses the continuous two form sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L339-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L339-L345

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

theorem ReciprocityTheory.L2DbarEstimates.F.continuous_two_form_sq (n : ℕ) : Continuous (sq2 n) := by sorry
