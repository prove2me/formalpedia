-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_kTypeIntDom_of
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.kTypeIntDom_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:58.71265+00:00
-- url     : https://prove2.me/theorems/c49d0064-76b3-5fb1-bf94-b2a722b859eb
-- title:
--   HW: k Type Int Dom of
-- statement:
--   The HW construction uses the k Type Int Dom of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/InnerLowerSelf.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/InnerLowerSelf.lean#L41-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_InnerLowerSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.kTypeIntDom_of
    (hint : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (_T : KType ε Λ), ∀ a, ∃ m : ℤ, Λ a = m) :
    KTypeIntDomStatement := by sorry
