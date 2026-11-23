-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_mem_of_ge
-- name    : ReciprocityTheory.ChartRestriction.DS.lowWord_mem_of_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:51.912618+00:00
-- url     : https://prove2.me/theorems/9f0f120d-7bf6-4ad1-81a3-83ff22ad3e04
-- title:
--   DS: low Word mem of ge
-- statement:
--   The DS construction uses the low Word mem of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L80-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L80-L90

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

theorem ReciprocityTheory.ChartRestriction.DS.lowWord_mem_of_ge (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : ∀ a, E a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a) (hε : ε a = ε b) :
    E a b (lowWord E y l) ∈ kLowSpan ε E y := by sorry
