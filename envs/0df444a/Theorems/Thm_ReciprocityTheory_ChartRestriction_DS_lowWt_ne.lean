-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWt_ne
-- name    : ReciprocityTheory.ChartRestriction.DS.lowWt_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:08.6728+00:00
-- url     : https://prove2.me/theorems/f1b4e6f7-6c69-462b-a4c3-5d05faa929a5
-- title:
--   DS: low Wt ne
-- statement:
--   The DS construction uses the low Wt ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L160-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L160-L170

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

theorem ReciprocityTheory.ChartRestriction.DS.lowWt_ne {μ : Fin n → ℝ} {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) (hne : l ≠ []) :
    lowWt μ l ≠ μ := by sorry
