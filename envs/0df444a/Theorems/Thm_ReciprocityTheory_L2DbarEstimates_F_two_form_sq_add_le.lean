-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_add_le
-- name    : ReciprocityTheory.L2DbarEstimates.F.two_form_sq_add_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:57.32669+00:00
-- url     : https://prove2.me/theorems/228f3eb1-7d4a-44e4-bb01-3e2d36041679
-- title:
--   F: two form sq add le
-- statement:
--   The F construction uses the two form sq add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L33-L42

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

theorem ReciprocityTheory.L2DbarEstimates.F.two_form_sq_add_le (n : ℕ) (a b : Fin n → Fin n → ℂ) :
    sq2 n (fun j k => a j k + b j k) ≤ 2 * sq2 n a + 2 * sq2 n b := by sorry
