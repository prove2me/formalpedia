-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_d__stable_of_stable_450b929b4aba
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_d__stable_of_stable_450b929b4aba
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:52.086918+00:00
-- url     : https://prove2.me/theorems/404ced63-3bbd-5682-9624-71634a22ae7d
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KRep d  stable of stable 450b929b4aba: P2 M Reciprocity Theory Chart Restriction DS HW KRep d  stable of stable 450b929b4aba
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KRep d  stable of stable 450b929b4aba construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KRep d  stable of stable 450b929b4aba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Stable.lean#L90-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Stable.lean#L90-L124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_d__stable_of_stable_450b929b4aba {ε : Fin n → Bool} (R : KRep ε)
    (W : Submodule ℂ R.V) (hW : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KRep».«dτ_stable_of_stable» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_d__stable_of_stable_450b929b4aba
