-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_not_injective_shift_iff
-- name    : ReciprocityTheory.ChartRestriction.DS.not_injective_shift_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:25.234734+00:00
-- url     : https://prove2.me/theorems/04205fd8-542c-47d2-8378-16b11f5f3fa4
-- title:
--   DS: not injective shift iff
-- statement:
--   The DS construction uses the not injective shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L118-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L118-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
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

theorem ReciprocityTheory.ChartRestriction.DS.not_injective_shift_iff {μ ν : Fin n → ℝ} (hμ : Function.Injective μ) (s : Fin n) (c : ℝ)
    (hs : ν s = μ s + c) (ho : ∀ x, x ≠ s → ν x = μ x) :
    ¬ Function.Injective ν ↔ ∃ s' ∈ univ.erase s, μ s + c = μ s' := by sorry
