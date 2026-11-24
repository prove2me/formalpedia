-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_hw_unique
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.KType.hw_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:11:50.006027+00:00
-- url     : https://prove2.me/theorems/28b8f8f9-e0a0-43c3-ae74-6fab744fddc0
-- title:
--   KType: hw unique
-- statement:
--   The KType construction uses the hw unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Weight.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Weight.lean#L34-L39

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.KType.hw_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ν : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (h : IsKHWVec ε (kunits T) ν v) : ν = Λ ∧ ∃ c : ℂ, v = c • T.w := by sorry
