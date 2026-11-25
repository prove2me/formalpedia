-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pPlus_card_eq_one
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pPlus_card_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:54.943732+00:00
-- url     : https://prove2.me/theorems/95bba536-1d57-4b7f-aa88-d812dc4003d5
-- title:
--   HW: p Plus card eq one
-- statement:
--   The HW construction uses the p Plus card eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PPlusPWtInjective.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PPlusPWtInjective.lean#L58-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PPlusPWtInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.pPlus_card_eq_one (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (p : pIdx ε β) :
    Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} = 1 := by sorry
