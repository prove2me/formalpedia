-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_norm_sq_le_two_form_sq
-- name    : ReciprocityTheory.L2DbarEstimates.F.norm_sq_le_two_form_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:28.436341+00:00
-- url     : https://prove2.me/theorems/c36ca7c9-7d71-4b9d-863e-e23947d15aea
-- title:
--   F: norm sq le two form sq
-- statement:
--   The F construction uses the norm sq le two form sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L12-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
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

theorem ReciprocityTheory.L2DbarEstimates.F.norm_sq_le_two_form_sq (n : ℕ) (σx : Fin n → Fin n → ℂ) : ‖σx‖ ^ 2 ≤ 2 * sq2 n σx := by sorry
