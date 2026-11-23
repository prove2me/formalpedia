-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_layer
-- name    : ReciprocityTheory.ChartRestriction.DS.finiteDimensional_layer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:22.358798+00:00
-- url     : https://prove2.me/theorems/356ae93b-aa86-4ca4-b77c-120491cbf534
-- title:
--   DS: finite Dimensional layer
-- statement:
--   The DS construction uses the finite Dimensional layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L93-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerBasic.lean#L93-L100

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

theorem ReciprocityTheory.ChartRestriction.DS.finiteDimensional_layer (hV : FiniteDimensional ℂ V) (k : ℕ) :
    FiniteDimensional ℂ (layer ε E V k) := by sorry
