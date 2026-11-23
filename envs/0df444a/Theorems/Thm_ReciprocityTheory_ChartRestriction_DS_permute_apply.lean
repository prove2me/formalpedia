-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_permute_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.permute_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:18.471245+00:00
-- url     : https://prove2.me/theorems/822a902e-21b9-4c20-a14f-72e8595da609
-- title:
--   DS: permute apply
-- statement:
--   The DS construction uses the permute apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L22-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := by sorry
