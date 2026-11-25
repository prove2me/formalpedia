-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieri_sum_finset_neg
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieri_sum_finset_neg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:28.600059+00:00
-- url     : https://prove2.me/theorems/3d087641-55ff-5e7b-89a1-e2a5a4050eb0
-- title:
--   HW: pieri sum finset neg
-- statement:
--   The HW construction uses the pieri sum finset neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L71-L75

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieri_sum_finset_neg {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ) (hu : Set.InjOn u S) :
    ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b - 1) / (u s - u b) = #S := by sorry
