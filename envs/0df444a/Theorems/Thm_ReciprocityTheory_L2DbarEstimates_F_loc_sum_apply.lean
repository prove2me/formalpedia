-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_sum_apply
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_sum_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:11.030627+00:00
-- url     : https://prove2.me/theorems/4ac3d515-42d0-5755-ac59-a92ab6093c9c
-- title:
--   F: loc sum apply
-- statement:
--   The F construction uses the loc sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L182-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L182-L189

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

theorem ReciprocityTheory.L2DbarEstimates.F.loc_sum_apply {n N : ℕ} (a : Fin N → V n) (j : Fin n) :
    (∑ i, a i) j = ∑ i, a i j := by sorry
