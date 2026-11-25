-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_add_ncSum_le
-- name    : ReciprocityTheory.ChartRestriction.DS.sqrt_nsq_add_ncSum_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:40.207692+00:00
-- url     : https://prove2.me/theorems/a853299e-cce3-4468-88d5-30c2e64906c1
-- title:
--   DS: sqrt nsq add nc Sum le
-- statement:
--   The DS construction uses the sqrt nsq add nc Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L77-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L77-L97

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

theorem ReciprocityTheory.ChartRestriction.DS.sqrt_nsq_add_ncSum_le {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω)
    (x : Fin n → ℝ) :
    √(nsq (x + ω)) ≤ √(nsq x) + √2 * j := by sorry
