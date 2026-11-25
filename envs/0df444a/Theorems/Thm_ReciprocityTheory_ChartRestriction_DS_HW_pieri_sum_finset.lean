-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieri_sum_finset
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieri_sum_finset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:27.22187+00:00
-- url     : https://prove2.me/theorems/32db455b-f051-5386-ba37-70c84615208b
-- title:
--   HW: pieri sum finset
-- statement:
--   The HW construction uses the pieri sum finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L67-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Polynomial Finset

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieri_sum_finset {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ) (hu : Set.InjOn u S) :
    ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b + 1) / (u s - u b) = #S := by sorry
