-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_card_pIdx
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylSum_card_pIdx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:54.970104+00:00
-- url     : https://prove2.me/theorems/4d0ac936-44a8-51b9-989a-1dc2eb6109f3
-- title:
--   HW: weyl Sum card p Idx
-- statement:
--   The HW construction uses the weyl Sum card p Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L49-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylSum_card_pIdx {n : ℕ} (ε : Fin n → Bool) (β : Bool) :
    (Nat.card (pIdx ε β) : ℝ) = ((univ.filter (fun i => ε i = β)).card : ℝ) *
      ((univ.filter (fun j => ε j = !β)).card : ℝ) := by sorry
