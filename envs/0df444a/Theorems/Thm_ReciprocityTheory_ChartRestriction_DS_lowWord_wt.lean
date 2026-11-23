-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_wt
-- name    : ReciprocityTheory.ChartRestriction.DS.lowWord_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:45.012819+00:00
-- url     : https://prove2.me/theorems/0d4ddec8-2aa2-4c9e-acb7-5cb56486bc2a
-- title:
--   DS: low Word wt
-- statement:
--   The DS construction uses the low Word wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L37-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L37-L59

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

theorem ReciprocityTheory.ChartRestriction.DS.lowWord_wt (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : ∀ a, E a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)) (a : Fin n),
      E a a (lowWord E y l) = (lowWt μ l a : ℂ) • lowWord E y l
  := by sorry
