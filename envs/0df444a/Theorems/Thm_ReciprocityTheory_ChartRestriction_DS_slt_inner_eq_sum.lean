-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_inner_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.slt_inner_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:59.128505+00:00
-- url     : https://prove2.me/theorems/5d45fa6d-783f-4e77-9938-a76282dbddab
-- title:
--   DS: slt inner eq sum
-- statement:
--   The DS construction uses the slt inner eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L50-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.slt_inner_eq_sum {k : ℕ} (i : Fin k) (A B : Big n k M) :
    inner ℂ A B = ∑ r, inner ℂ (slt i r A) (slt i r B) := by sorry
