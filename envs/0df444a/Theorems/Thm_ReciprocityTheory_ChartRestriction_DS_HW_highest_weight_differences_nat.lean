-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_highest_weight_differences_nat
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.highest_weight_differences_nat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:45:02.666885+00:00
-- url     : https://prove2.me/theorems/7642688d-1e46-4625-9f34-3d7a686b0539
-- title:
--   HW: highest weight differences nat
-- statement:
--   The HW construction uses the highest weight differences nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L120-L129

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.highest_weight_differences_nat (hF : Formalism.REAL.KRel ε F) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : IsKStableSub ε F S) {μ : Fin n → ℝ} {v : M} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hw : IsKHWVec ε F μ v) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, μ a - μ b = m := by sorry
