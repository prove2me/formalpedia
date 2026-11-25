-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_pair_apply_khw
-- name    : ReciprocityTheory.ChartRestriction.DS.pair_apply_khw
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:22.09687+00:00
-- url     : https://prove2.me/theorems/958fd8f1-0c6c-4886-afcb-ab1df45963b3
-- title:
--   DS: pair apply khw
-- statement:
--   The DS construction uses the pair apply khw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L179-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L179-L194

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
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
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.pair_apply_khw {E : Fin n → Fin n → Module.End ℂ W} {μ : Fin n → ℝ} {v : W} {a b : Fin n}
    (hc : E a b * E b a - E b a * E a b = E a a - E b b) (hd : ∀ a, E a a v = (μ a : ℂ) • v)
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by sorry
