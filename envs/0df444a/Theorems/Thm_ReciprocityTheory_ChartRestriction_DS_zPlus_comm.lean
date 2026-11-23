-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_zPlus_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.zPlus_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:29.990134+00:00
-- url     : https://prove2.me/theorems/4c9b727f-391c-47ae-b7f6-d005f460f9a9
-- title:
--   DS: z Plus comm
-- statement:
--   The DS construction uses the z Plus comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L177-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L177-L189

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.zPlus_comm {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    zPlus ε E * E a b = E a b * zPlus ε E +
      ((if ε a = true then (1 : ℂ) else 0) - (if ε b = true then (1 : ℂ) else 0)) • E a b := by sorry
