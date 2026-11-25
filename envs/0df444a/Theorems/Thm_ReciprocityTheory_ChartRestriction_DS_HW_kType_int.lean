-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_kType_int
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.kType_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:52.61292+00:00
-- url     : https://prove2.me/theorems/3ab3d902-121f-4847-9c58-f6d7326570a7
-- title:
--   HW: k Type int
-- statement:
--   The HW construction uses the k Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KtintExpApplyOfEig.lean#L79-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KtintExpApplyOfEig.lean#L79-L122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.kType_int {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : ∀ a, ∃ m : ℤ, Λ a = m := by sorry
