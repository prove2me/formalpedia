-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:37.731271+00:00
-- url     : https://prove2.me/theorems/b0542006-8ae1-4e5c-81d4-3ea5aaa27bc7
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW in K conj  14f76c740320: P2 M Reciprocity Theory Chart Restriction DS HW in K conj  14f76c740320
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW in K conj  14f76c740320 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW in K conj  14f76c740320 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L70-L86

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320 {ε : Fin n → Bool} (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    inK ε (toMK k * Y * star (toMK k)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«inK_conj'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320
