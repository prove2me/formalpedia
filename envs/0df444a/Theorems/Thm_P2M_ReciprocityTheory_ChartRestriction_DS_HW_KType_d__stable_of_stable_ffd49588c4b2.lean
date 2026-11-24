-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:24.374816+00:00
-- url     : https://prove2.me/theorems/6ae43dd7-d00f-484d-8bfe-b96f4f9b0c9a
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KType d  stable of stable ffd49588c4b2: P2 M Reciprocity Theory Chart Restriction DS HW KType d  stable of stable ffd49588c4b2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KType d  stable of stable ffd49588c4b2 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KType d  stable of stable ffd49588c4b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L93-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L93-L157

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2 {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (W : Submodule ℂ T.V) (hW : ∀ k : KG ε, ∀ v ∈ W, T.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, T.dτ (Matrix.single a b 1) v ∈ W := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KType».«dτ_stable_of_stable» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2
