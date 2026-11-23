-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_hwTerm
-- name    : ReciprocityTheory.ChartRestriction.DS.sum_hwTerm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:31.422037+00:00
-- url     : https://prove2.me/theorems/659a3fb0-d0ba-48c7-af62-372114714214
-- title:
--   DS: sum hw Term
-- statement:
--   The DS construction uses the sum hw Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/CasimirKKhwVec.lean#L46-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/CasimirKKhwVec.lean#L46-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.sum_hwTerm (S : Fin n → Fin n → Prop) [DecidableRel S] (hrefl : ∀ a, S a a)
    (hS : ∀ a b, S a b → S b a) (μ r : Fin n → ℝ)
    (hr : ∀ a, 2 * r a = ((univ.filter fun b => a < b ∧ S a b).card : ℝ) -
      ((univ.filter fun b => b < a ∧ S a b).card : ℝ)) :
    ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b = nsq (μ + r) - nsq r := by sorry
