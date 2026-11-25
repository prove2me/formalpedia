-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_slice_mem_ncV
-- name    : ReciprocityTheory.ChartRestriction.DS.slt_slice_mem_ncV
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:38.374369+00:00
-- url     : https://prove2.me/theorems/7c953ca3-2b5c-57a1-8a0d-44ef7c5722cd
-- title:
--   DS: slt slice mem nc V
-- statement:
--   The DS construction uses the slt slice mem nc V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L119-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L119-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.slt_slice_mem_ncV {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slice i κ F ∈ ncV ε V 1 := by sorry
