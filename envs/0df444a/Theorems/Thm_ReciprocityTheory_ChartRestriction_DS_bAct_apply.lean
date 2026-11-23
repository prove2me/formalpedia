-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.bAct_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:13.040621+00:00
-- url     : https://prove2.me/theorems/20e93c9f-cf8f-42d6-b1c1-1ea20d1de0d3
-- title:
--   DS: b Act apply
-- statement:
--   The DS construction uses the b Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L98-L103

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

theorem ReciprocityTheory.ChartRestriction.DS.bAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (bAct E k a b F) κ = E a b (F κ) + ∑ i, (factorAd k i a b F) κ := by sorry
