-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_kType_unique
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.kType_unique
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:47.281674+00:00
-- url     : https://prove2.me/theorems/acd031d4-bf3f-4eb6-9875-06592a608894
-- title:
--   HW: k Type unique
-- statement:
--   The HW construction uses the k Type unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Unique.lean#L30-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Unique.lean#L30-L81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.kType_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T T' : KType ε Λ) :
    ∃ φ : T.V ≃ₗᵢ[ℂ] T'.V, (∀ (k : KG ε) (v : T.V), φ (T.op k v) = T'.op k (φ v)) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X → ∀ v : T.V, φ (T.dτ X v) = T'.dτ X (φ v)) ∧
      φ T.w = T'.w := by sorry
