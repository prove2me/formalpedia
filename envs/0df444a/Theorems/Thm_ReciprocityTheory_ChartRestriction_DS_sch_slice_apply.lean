-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_slice_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.sch_slice_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:29.69107+00:00
-- url     : https://prove2.me/theorems/df058024-7fa6-477f-9d0f-531e0c64bb46
-- title:
--   DS: sch slice apply
-- statement:
--   The DS construction uses the sch slice apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchPhiOneApply.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchPhiOneApply.lean#L56-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply
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

theorem ReciprocityTheory.ChartRestriction.DS.sch_slice_apply {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M)
    (ι : Fin 1 → Fin n × Fin n) : slice i κ F ι = F (Function.update κ i (ι 0)) := by sorry
