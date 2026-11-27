-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_permute_mem_ncV
-- name    : ReciprocityTheory.ChartRestriction.DS.permute_mem_ncV
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:13.81323+00:00
-- url     : https://prove2.me/theorems/1901f899-a546-4845-8003-de46b4955e60
-- title:
--   DS: permute mem nc V
-- statement:
--   The DS construction uses the permute mem nc V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L29-L45

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

theorem ReciprocityTheory.ChartRestriction.DS.permute_mem_ncV {k : ℕ} (σ : Equiv.Perm (Fin k)) {F : Big n k M} (hF : F ∈ ncV ε V k) :
    permute σ F ∈ ncV ε V k := by sorry
