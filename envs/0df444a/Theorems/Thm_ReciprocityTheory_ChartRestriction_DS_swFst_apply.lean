-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_swFst_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.swFst_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:35.681965+00:00
-- url     : https://prove2.me/theorems/7ae51b18-d18f-4315-a74c-10a69e96eff0
-- title:
--   DS: sw Fst apply
-- statement:
--   The DS construction uses the sw Fst apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L113-L114

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

theorem ReciprocityTheory.ChartRestriction.DS.swFst_apply {k : ℕ} (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n) :
    swFst i a b κ = Function.update κ i (Equiv.swap a b (κ i).1, (κ i).2) := by sorry
