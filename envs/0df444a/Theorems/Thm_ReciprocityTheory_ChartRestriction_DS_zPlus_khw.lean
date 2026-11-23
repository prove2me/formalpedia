-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_zPlus_khw
-- name    : ReciprocityTheory.ChartRestriction.DS.zPlus_khw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:22.385512+00:00
-- url     : https://prove2.me/theorems/ab213c6c-ca3e-416a-97af-41cd406817ec
-- title:
--   DS: z Plus khw
-- statement:
--   The DS construction uses the z Plus khw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L191-L195

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

theorem ReciprocityTheory.ChartRestriction.DS.zPlus_khw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {ν : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E ν w) : zPlus ε E w = (∑ c ∈ plusIdx ε, ((ν c : ℝ) : ℂ)) • w := by sorry
