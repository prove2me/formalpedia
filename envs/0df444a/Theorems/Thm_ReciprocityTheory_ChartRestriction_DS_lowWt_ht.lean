-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWt_ht
-- name    : ReciprocityTheory.ChartRestriction.DS.lowWt_ht
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:52.659068+00:00
-- url     : https://prove2.me/theorems/7c0e1285-61e0-52e5-a0c9-9ee00422b8e5
-- title:
--   DS: low Wt ht
-- statement:
--   The DS construction uses the low Wt ht property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L146-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L146-L158

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
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
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.lowWt_ht (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) →
      (∑ i : Fin n, ((i : ℕ) : ℝ) * μ i) + l.length ≤ ∑ i : Fin n, ((i : ℕ) : ℝ) * lowWt μ l i
  := by sorry
