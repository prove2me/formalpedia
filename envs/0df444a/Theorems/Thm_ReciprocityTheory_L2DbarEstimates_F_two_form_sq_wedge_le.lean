-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_wedge_le
-- name    : ReciprocityTheory.L2DbarEstimates.F.two_form_sq_wedge_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:03.775716+00:00
-- url     : https://prove2.me/theorems/84ef4042-7f27-5251-9ace-7b127b43209c
-- title:
--   F: two form sq wedge le
-- statement:
--   The F construction uses the two form sq wedge le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L49-L68

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

theorem ReciprocityTheory.L2DbarEstimates.F.two_form_sq_wedge_le (n : ℕ) (a b : Fin n → ℂ) :
    sq2 n (wedge a b) ≤ 2 * (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by sorry
