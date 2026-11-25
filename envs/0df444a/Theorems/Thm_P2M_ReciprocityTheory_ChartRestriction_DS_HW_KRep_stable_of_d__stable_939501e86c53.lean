-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_stable_of_d__stable_939501e86c53
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_stable_of_d__stable_939501e86c53
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:45.650083+00:00
-- url     : https://prove2.me/theorems/4243b5f8-6359-4324-a5c7-b422ef7a1004
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KRep stable of d  stable 939501e86c53: P2 M Reciprocity Theory Chart Restriction DS HW KRep stable of d  stable 939501e86c53
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KRep stable of d  stable 939501e86c53 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KRep stable of d  stable 939501e86c53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Stable.lean#L126-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Stable.lean#L126-L143

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_stable_of_d__stable_939501e86c53 {ε : Fin n → Bool} (R : KRep ε) (W : Submodule ℂ R.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W) :
    ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KRep».«stable_of_dτ_stable» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_stable_of_d__stable_939501e86c53
