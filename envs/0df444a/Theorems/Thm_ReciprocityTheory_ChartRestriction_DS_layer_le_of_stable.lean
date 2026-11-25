-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_of_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.layer_le_of_stable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:53.691597+00:00
-- url     : https://prove2.me/theorems/f65d5866-b243-48ae-9c32-bfc3d1970c8c
-- title:
--   DS: layer le of stable
-- statement:
--   The DS construction uses the layer le of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L31-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.layer_le_of_stable {T : Submodule ℂ M} (hVT : V ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) (k : ℕ) : layer ε E V k ≤ T := by sorry
