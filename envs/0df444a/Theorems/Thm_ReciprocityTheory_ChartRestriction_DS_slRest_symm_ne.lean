-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slRest_symm_ne
-- name    : ReciprocityTheory.ChartRestriction.DS.slRest_symm_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:13.751549+00:00
-- url     : https://prove2.me/theorems/810c76bf-4300-514e-a0b9-aa0245436e62
-- title:
--   DS: sl Rest symm ne
-- statement:
--   The DS construction uses the sl Rest symm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L108-L110

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

theorem ReciprocityTheory.ChartRestriction.DS.slRest_symm_ne {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n)
    {j : Fin k} (h : j ≠ i) : (slRest i).symm (p, r) j = r ⟨j, h⟩ := by sorry
