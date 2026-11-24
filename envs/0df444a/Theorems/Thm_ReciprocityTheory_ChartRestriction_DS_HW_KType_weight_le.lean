-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_weight_le
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.KType.weight_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:11:03.572725+00:00
-- url     : https://prove2.me/theorems/8bfa8ad0-69ae-47c8-8538-16121183218b
-- title:
--   KType: weight le
-- statement:
--   The KType construction uses the weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Weight.lean#L78-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Weight.lean#L78-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.KType.weight_le {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (hμ : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b := by sorry
