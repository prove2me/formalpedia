-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_zPlus_V
-- name    : ReciprocityTheory.ChartRestriction.DS.zPlus_V
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:32.763039+00:00
-- url     : https://prove2.me/theorems/217f76fd-57bb-5bff-9128-5b3bdc0d00e1
-- title:
--   DS: z Plus V
-- statement:
--   The DS construction uses the z Plus V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L197-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L197-L225

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

theorem ReciprocityTheory.ChartRestriction.DS.zPlus_V {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E Λ V) :
    ∀ v ∈ V, zPlus ε E v = (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • v := by sorry
