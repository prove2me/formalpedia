-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_nat_weight_sub_eq_of_highest_vector_in_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:58:30.890536+00:00
-- url     : https://prove2.me/theorems/80fcb6d4-3eb3-4fcb-9ca4-75e6a2aa0833
-- title:
--   HW: exists nat weight sub eq of highest vector in stable
-- statement:
--   The HW construction uses the exists nat weight sub eq of highest vector in stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L49-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L49-L118

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
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
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    (S : Submodule ℂ M) [FiniteDimensional ℂ S] (hS : ∀ y ∈ S, F b a y ∈ S)
    {v : M} (hv : v ∈ S) (hv0 : v ≠ 0) {la lb : ℂ} (ha : F a a v = la • v) (hb : F b b v = lb • v)
    (h0 : F a b v = 0) : ∃ m : ℕ, la - lb = m := by sorry
