-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_mul__6ba5f44adf8c
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_mul__6ba5f44adf8c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:54.41428+00:00
-- url     : https://prove2.me/theorems/76b898f5-0a2f-4792-b238-786258bb83e7
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW to MK mul  6ba5f44adf8c: P2 M Reciprocity Theory Chart Restriction DS HW to MK mul  6ba5f44adf8c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW to MK mul  6ba5f44adf8c construction uses the P2 M Reciprocity Theory Chart Restriction DS HW to MK mul  6ba5f44adf8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean#L67-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_mul__6ba5f44adf8c (ε : Fin n → Bool) (x k : KG ε) : toMK (x * k) = toMK x * toMK k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«toMK_mul'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_mul__6ba5f44adf8c
