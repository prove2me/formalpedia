-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_block_filter_eq_erase
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.block_filter_eq_erase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:51.486731+00:00
-- url     : https://prove2.me/theorems/e526059a-36cd-47bc-a233-336ec7b18e2a
-- title:
--   HW: block filter eq erase
-- statement:
--   The HW construction uses the block filter eq erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L77-L80

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.block_filter_eq_erase {n : ℕ} (ε : Fin n → Bool) (β : Bool) {s : Fin n} (hs : ε s = β) :
    univ.filter (fun b => b ≠ s ∧ ε b = ε s) = (univ.filter (fun b => ε b = β)).erase s := by sorry
