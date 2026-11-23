-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blockSum_plus
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.blockSum_plus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:39.659825+00:00
-- url     : https://prove2.me/theorems/07d380cf-b7f3-4796-8706-7979b61c77a8
-- title:
--   HW: block Sum plus
-- statement:
--   The HW construction uses the block Sum plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L82-L88

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.blockSum_plus {n : ℕ} (ε : Fin n → Bool) (β : Bool) (u : Fin n → ℝ)
    (hu : ∀ a b, ε a = β → ε b = β → u a = u b → a = b) :
    ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      (u s - u b + 1) / (u s - u b) = ((univ.filter (fun s => ε s = β)).card : ℝ) := by sorry
