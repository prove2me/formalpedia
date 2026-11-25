-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_swSnd_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.swSnd_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:55.060277+00:00
-- url     : https://prove2.me/theorems/6cf4aab3-4b1a-46e4-8505-3e093a3a5339
-- title:
--   DS: sw Snd apply
-- statement:
--   The DS construction uses the sw Snd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L116-L117

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

theorem ReciprocityTheory.ChartRestriction.DS.swSnd_apply {k : ℕ} (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n) :
    swSnd i a b κ = Function.update κ i ((κ i).1, Equiv.swap a b (κ i).2) := by sorry
