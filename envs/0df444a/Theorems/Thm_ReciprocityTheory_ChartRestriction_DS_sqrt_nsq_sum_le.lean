-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_sum_le
-- name    : ReciprocityTheory.ChartRestriction.DS.sqrt_nsq_sum_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:26.968473+00:00
-- url     : https://prove2.me/theorems/fb98918c-d123-51a2-b89f-7c82cbf8a14e
-- title:
--   DS: sqrt nsq sum le
-- statement:
--   The DS construction uses the sqrt nsq sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L68-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
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

theorem ReciprocityTheory.ChartRestriction.DS.sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by sorry
