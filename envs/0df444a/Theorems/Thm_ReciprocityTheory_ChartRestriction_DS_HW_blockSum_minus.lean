-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blockSum_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.blockSum_minus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:42.609562+00:00
-- url     : https://prove2.me/theorems/09419795-6a13-491f-9972-68283dab802a
-- title:
--   HW: block Sum minus
-- statement:
--   The HW construction uses the block Sum minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/BlockSum.lean#L90-L96

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.blockSum_minus {n : ℕ} (ε : Fin n → Bool) (β : Bool) (u : Fin n → ℝ)
    (hu : ∀ a b, ε a = β → ε b = β → u a = u b → a = b) :
    ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      (u s - u b - 1) / (u s - u b) = ((univ.filter (fun s => ε s = β)).card : ℝ) := by sorry
