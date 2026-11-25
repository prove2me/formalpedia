-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slice_eq_slt
-- name    : ReciprocityTheory.ChartRestriction.DS.slice_eq_slt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:32.308887+00:00
-- url     : https://prove2.me/theorems/38a24723-98f7-40ab-a132-b7e7bce3ae4c
-- title:
--   DS: slice eq slt
-- statement:
--   The DS construction uses the slice eq slt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L42-L44

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
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.slice_eq_slt {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (A : Big n k M) :
    slice i κ A = slt i (slRest i κ).2 A := by sorry
