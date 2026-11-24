-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_pIdx
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylSum_pIdx
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:11.15512+00:00
-- url     : https://prove2.me/theorems/f50b7720-c4e7-4df3-a953-8e792a130a2e
-- title:
--   HW: weyl Sum p Idx
-- statement:
--   The HW construction uses the weyl Sum p Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L43-L47

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylSum_pIdx {n : ℕ} (ε : Fin n → Bool) (β : Bool) (F G : Fin n → ℝ) :
    ∑ p : pIdx ε β, F p.1.1 * G p.1.2 =
      (∑ i ∈ univ.filter (fun i => ε i = β), F i) * ∑ j ∈ univ.filter (fun j => ε j = !β), G j := by sorry
