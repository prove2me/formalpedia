-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_finset_sum_le
-- name    : ReciprocityTheory.L2DbarEstimates.F.two_form_sq_finset_sum_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:00.744957+00:00
-- url     : https://prove2.me/theorems/1f148557-6da6-4946-a7cc-5a6f8a9ecdc7
-- title:
--   F: two form sq finset sum le
-- statement:
--   The F construction uses the two form sq finset sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L130-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L130-L142

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.two_form_sq_finset_sum_le {n N : ℕ} (σ : Fin N → Fin n → Fin n → ℂ) :
    sq2 n (fun j k => ∑ i, σ i j k) ≤ N * ∑ i, sq2 n (σ i) := by sorry
