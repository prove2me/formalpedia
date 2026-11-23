-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_crossOp
-- name    : ReciprocityTheory.ChartRestriction.DS.slt_crossOp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:10.54779+00:00
-- url     : https://prove2.me/theorems/cc1f8ce4-8703-46c3-9231-d585beb5ebeb
-- title:
--   DS: slt cross Op
-- statement:
--   The DS construction uses the slt cross Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L90-L94

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

theorem ReciprocityTheory.ChartRestriction.DS.slt_crossOp {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) :
    slt i r (crossOp ε E k i A) = crossOp ε E 1 0 (slt i r A) := by sorry
