-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_layer_succ_nc
-- name    : ReciprocityTheory.ChartRestriction.DS.apply_mem_layer_succ_nc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:18.935423+00:00
-- url     : https://prove2.me/theorems/cc1efab5-fd12-4b78-9361-8bc0cba53937
-- title:
--   DS: apply mem layer succ nc
-- statement:
--   The DS construction uses the apply mem layer succ nc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L24-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.apply_mem_layer_succ_nc {a b : Fin n} (hab : ε a ≠ ε b) {k : ℕ} {v : M}
    (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by sorry
