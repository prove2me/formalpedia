-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.ncV_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:10.570714+00:00
-- url     : https://prove2.me/theorems/d9f65022-cf09-44ea-b3df-4b667dd982dd
-- title:
--   DS: nc V eq zero
-- statement:
--   The DS construction uses the nc V eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L163-L167

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
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

theorem ReciprocityTheory.ChartRestriction.DS.ncV_eq_zero {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) {κ : Fin k → Fin n × Fin n}
    (j : Fin k) (hj : ε (κ j).1 = ε (κ j).2) : F κ = 0 := by sorry
