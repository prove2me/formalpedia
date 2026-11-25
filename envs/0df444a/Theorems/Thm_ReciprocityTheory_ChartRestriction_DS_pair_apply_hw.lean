-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_pair_apply_hw
-- name    : ReciprocityTheory.ChartRestriction.DS.pair_apply_hw
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:52.608793+00:00
-- url     : https://prove2.me/theorems/c292bf67-6b9a-41e6-96c6-e26380002c2e
-- title:
--   DS: pair apply hw
-- statement:
--   The DS construction uses the pair apply hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/CasimirKKhwVec.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/CasimirKKhwVec.lean#L18-L32

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

theorem ReciprocityTheory.ChartRestriction.DS.pair_apply_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (hd : ∀ a, E a a v = (μ a : ℂ) • v) {a b : Fin n}
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by sorry
