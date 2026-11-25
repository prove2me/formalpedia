-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_eq_slice
-- name    : ReciprocityTheory.ChartRestriction.DS.slt_eq_slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:47.454823+00:00
-- url     : https://prove2.me/theorems/4ada96c1-a3ee-4173-8f89-1da958ef3c48
-- title:
--   DS: slt eq slice
-- statement:
--   The DS construction uses the slt eq slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L112-L114

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

theorem ReciprocityTheory.ChartRestriction.DS.slt_eq_slice {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (p : Fin n × Fin n)
    (A : Big n k M) : slt i r A = slice i ((slRest i).symm (p, r)) A := by sorry
