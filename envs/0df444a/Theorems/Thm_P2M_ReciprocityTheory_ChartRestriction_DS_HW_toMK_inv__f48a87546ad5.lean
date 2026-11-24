-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_inv__f48a87546ad5
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_inv__f48a87546ad5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:27.095669+00:00
-- url     : https://prove2.me/theorems/187adada-e0c5-45a9-b301-c08120e9f164
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW to MK inv  f48a87546ad5: P2 M Reciprocity Theory Chart Restriction DS HW to MK inv  f48a87546ad5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW to MK inv  f48a87546ad5 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW to MK inv  f48a87546ad5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L39-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
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
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_inv__f48a87546ad5 {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = star (toMK k) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«toMK_inv'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_inv__f48a87546ad5
