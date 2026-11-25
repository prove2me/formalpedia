-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_pair_hw
-- name    : ReciprocityTheory.ChartRestriction.DS.sum_pair_hw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:10.507546+00:00
-- url     : https://prove2.me/theorems/285efc38-ffeb-4396-bc90-9ffccfcaf5c9
-- title:
--   DS: sum pair hw
-- statement:
--   The DS construction uses the sum pair hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/CasimirKKhwVec.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/CasimirKKhwVec.lean#L34-L42

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.sum_pair_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (S : Fin n → Fin n → Prop) [DecidableRel S] (hS : ∀ a b, S a b → S b a)
    (hd : ∀ a, E a a v = (μ a : ℂ) • v) (hv : ∀ a b, a < b → S a b → E a b v = 0) :
    (∑ a, ∑ b ∈ univ.filter (fun b => S a b), E a b * E b a) v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b : ℝ) : ℂ) • v := by sorry
