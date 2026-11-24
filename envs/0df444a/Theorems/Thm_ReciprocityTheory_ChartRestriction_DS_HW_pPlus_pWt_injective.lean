-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pPlus_pWt_injective
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pPlus_pWt_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:06.316768+00:00
-- url     : https://prove2.me/theorems/7a4b9c5f-5ca7-4522-9728-ab879cc81c9e
-- title:
--   HW: p Plus p Wt injective
-- statement:
--   The HW construction uses the p Plus p Wt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PPlusPWtInjective.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PPlusPWtInjective.lean#L40-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pPlus_pWt_injective (ε : Fin n → Bool) (β : Bool) : Function.Injective (pWt ε β) := by sorry
